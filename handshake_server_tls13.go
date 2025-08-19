// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package tls

import (
	"bytes"
	"context"
	"crypto"
	"crypto/hmac"
	"crypto/rsa"
	"crypto/subtle"
	"encoding/binary"
	"errors"
	"hash"
	"io"
	"sync/atomic"
	"time"
)

// maxClientPSKIdentities is the number of client PSK identities the server will
// attempt to validate. It will ignore the rest not to let cheap ClientHello
// messages cause too much work in session ticket decryption attempts.
const maxClientPSKIdentities = 5

type serverHandshakeStateTLS13 struct {
	c               *Conn
	ctx             context.Context
	clientHello     *clientHelloMsg
	hello           *serverHelloMsg
	sentDummyCCS    bool
	usingPSK        bool
	suite           *cipherSuiteTLS13
	cert            *Certificate
	sigAlg          SignatureScheme
	earlySecret     []byte
	sharedKey       []byte
	handshakeSecret []byte
	masterSecret    []byte
	trafficSecret   []byte // client_application_traffic_secret_0
	transcript      hash.Hash
	clientFinished  []byte
	
	// EXTLS modification: track the authentication status
	// EXTLS 认证状态，用于控制后续行为
	isExtls bool
}

func (hs *serverHandshakeStateTLS13) handshake() error {
	c := hs.c

	// For an overview of the TLS 1.3 handshake, see RFC 8446, Section 2.
	if err := hs.processClientHello(); err != nil {
		return err
	}
	if err := hs.checkForResumption(); err != nil {
		return err
	}
	if err := hs.pickCertificate(); err != nil {
		return err
	}
	c.buffering = true
	if err := hs.sendServerParameters(); err != nil {
		return err
	}
	if err := hs.sendServerCertificate(); err != nil {
		return err
	}

	// Now, we are ready to send our Finished message.
	// 在这里，我们将根据 isExtls 状态来决定是否修改 Finished 包。
	// We need to modify the finished message marshaling/unmarshaling process.
	// Instead of a simplified wrapper, we will modify the `finishedMsg` structure directly.

	// Calculate finished message.
	finished := new(finishedMsg)
	finished.verifyData = hs.c.finishedHash.serverSum(hs.masterSecret)

	if hs.isExtls {
		// If it's an EXTLS handshake, modify the finished message before sending.
		// The modification is XORing the first 8 bytes with HMAC(ServerRandom | ClientRandom).
		
		// 1. Calculate the HMAC key for XOR.
		h := hmac.New(crypto.SHA256.New, hs.c.config.EXTLSAuthKey)
		h.Write(hs.hello.random) // ServerRandom
		h.Write(hs.clientHello.random) // ClientRandom
		xorKey := h.Sum(nil)

		// 2. XOR the verifyData of the finished message.
		if len(finished.verifyData) >= 8 {
			for i := 0; i < 8; i++ {
				finished.verifyData[i] ^= xorKey[i]
			}
		}
	}

	// Now send the (potentially modified) finished message.
	if _, err := hs.c.writeHandshakeMsg(finished.marshal()); err != nil {
		return err
	}
	hs.transcript.Write(finished.marshal())

	// Note that at this point we could start sending application data without
	// waiting for the client's second flight, but the application might not
	// expect the lack of replay protection of the ClientHello parameters.
	if _, err := c.flush(); err != nil {
		return err
	}
	if err := hs.readClientCertificate(); err != nil {
		return err
	}
	if err := hs.readClientFinished(); err != nil {
		return err
	}

	atomic.StoreUint32(&c.handshakeStatus, 1)

	return nil
}

func (hs *serverHandshakeStateTLS13) processClientHello() error {
	c := hs.c

	hs.hello = new(serverHelloMsg)

	// TLS 1.3 froze the ServerHello.legacy_version field, and uses
	// supported_versions instead. See RFC 8446, sections 4.1.3 and 4.2.1.
	hs.hello.vers = VersionTLS12
	hs.hello.supportedVersion = c.vers

	if len(hs.clientHello.supportedVersions) == 0 {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: client used the legacy version field to negotiate TLS 1.3")
	}

	// Abort if the client is doing a fallback and landing lower than what we
	// support. See RFC 7507, which however does not specify the interaction
	// with supported_versions. The only difference is that with
	// supported_versions a client has a chance to attempt a [TLS 1.2, TLS 1.4]
	// handshake in case TLS 1.3 is broken but 1.2 is not. Alas, in that case,
	// it will have to drop the TLS_FALLBACK_SCSV protection if it falls back to
	// TLS 1.2, because a TLS 1.3 server would abort here. The situation before
	// supported_versions was not better because there was just no way to do a
	// TLS 1.4 handshake without risking the server selecting TLS 1.3.
	for _, id := range hs.clientHello.cipherSuites {
		if id == TLS_FALLBACK_SCSV {
			// Use c.vers instead of max(supported_versions) because an attacker
			// could defeat this by adding an arbitrary high version otherwise.
			if c.vers < c.config.maxSupportedVersion(roleServer) {
				c.sendAlert(alertInappropriateFallback)
				return errors.New("tls: client using inappropriate protocol fallback")
			}
			break
		}
	}
	
	var clientPublicKey []byte
	for _, ks := range hs.clientHello.keyShares {
		clientPublicKey = ks.data
		break
	}
	
	// 从 c.config 中获取 EXTLS 密钥
	authKey := hs.c.config.EXTLSAuthKey 
	
	// 检查是否为 EXTLS 客户端（通过 sessionId 长度和 clientPublicKey 存在判断）
	isExtlsClient := len(authKey) > 0 && len(clientPublicKey) > 0 && len(hs.clientHello.sessionId) == 32
	
	if isExtlsClient {
		h := hmac.New(crypto.SHA256.New, authKey)
		h.Write(clientPublicKey)
		expectedHMAC := h.Sum(nil)
		
		// 使用 ConstantTimeCompare 防止时序攻击
		if subtle.ConstantTimeCompare(expectedHMAC, hs.clientHello.sessionId) == 1 {
			// HMAC 匹配，认证成功
			hs.isExtls = true
		} else {
			// HMAC 不匹配，认证失败，但不是致命错误
			hs.isExtls = false
		}
	} else {
		// 不是 EXTLS 客户端，继续正常握手
		hs.isExtls = false
	}


	if len(hs.clientHello.compressionMethods) != 1 ||
		hs.clientHello.compressionMethods[0] != compressionNone {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: TLS 1.3 client supports illegal compression methods")
	}

	hs.hello.random = make([]byte, 32)
	if _, err := io.ReadFull(c.config.rand(), hs.hello.random); err != nil {
		c.sendAlert(alertInternalError)
		return err
	}

	if len(hs.clientHello.secureRenegotiation) != 0 {
		c.sendAlert(alertHandshakeFailure)
		return errors.New("tls: initial handshake had non-empty renegotiation extension")
	}

	if hs.clientHello.earlyData {
		// See RFC 8446, Section 4.2.10 for the complicated behavior required
		// here. The scenario is that a different server at our address offered
		// to accept early data in the past, which we can't handle. For now, all
		// 0-RTT enabled session tickets need to expire before a Go server can
		// replace a server or join a pool. That's the same requirement that
		// applies to mixing or replacing with any TLS 1.2 server.
		c.sendAlert(alertUnsupportedExtension)
		return errors.New("tls: client sent unexpected early data")
	}

	hs.hello.sessionId = hs.clientHello.sessionId
	hs.hello.compressionMethod = compressionNone

	preferenceList := defaultCipherSuitesTLS13
	if !hasAESGCMHardwareSupport || !aesgcmPreferred(hs.clientHello.cipherSuites) {
		preferenceList = defaultCipherSuitesTLS13NoAES
	}
	for _, suiteID := range preferenceList {
		hs.suite = mutualCipherSuiteTLS13(hs.clientHello.cipherSuites, suiteID)
		if hs.suite != nil {
			break
		}
	}
	if hs.suite == nil {
		c.sendAlert(alertHandshakeFailure)
		return errors.New("tls: no cipher suite supported by both client and server")
	}
	c.cipherSuite = hs.suite.id
	hs.hello.cipherSuite = hs.suite.id
	hs.transcript = hs.suite.hash.New()

	// Pick the ECDHE group in server preference order, but give priority to
	// groups with a key share, to avoid a HelloRetryRequest round-trip.
	var selectedGroup CurveID
	var clientKeyShare *keyShare
GroupSelection:
	for _, preferredGroup := range c.config.curvePreferences() {
		for _, ks := range hs.clientHello.keyShares {
			if ks.group == preferredGroup {
				selectedGroup = ks.group
				clientKeyShare = &ks
				break GroupSelection
			}
		}
		if selectedGroup != 0 {
			continue
		}
		for _, group := range hs.clientHello.supportedCurves {
			if group == preferredGroup {
				selectedGroup = group
				break
			}
		}
	}
	if selectedGroup == 0 {
		c.sendAlert(alertHandshakeFailure)
		return errors.New("tls: no ECDHE curve supported by both client and server")
	}
	if clientKeyShare == nil {
		if err := hs.doHelloRetryRequest(selectedGroup); err != nil {
			return err
		}
		clientKeyShare = &hs.clientHello.keyShares[0]
	}

	if _, ok := curveForCurveID(selectedGroup); selectedGroup != X25519 && !ok {
		c.sendAlert(alertInternalError)
		return errors.New("tls: CurvePreferences includes unsupported curve")
	}
	params, err := generateECDHEParameters(c.config.rand(), selectedGroup)
	if err != nil {
		c.sendAlert(alertInternalError)
		return err
	}
	hs.hello.serverShare = keyShare{group: selectedGroup, data: params.PublicKey()}
	hs.sharedKey = params.SharedKey(clientKeyShare.data)
	if hs.sharedKey == nil {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: invalid client key share")
	}

	c.serverName = hs.clientHello.serverName
	return nil
}

func (hs *serverHandshakeStateTLS13) checkForResumption() error {
	c := hs.c

	if c.config.SessionTicketsDisabled {
		return nil
	}

	modeOK := false
	for _, mode := range hs.clientHello.pskModes {
		if mode == pskModeDHE {
			modeOK = true
			break
		}
	}
	if !modeOK {
		return nil
	}

	if len(hs.clientHello.pskIdentities) != len(hs.clientHello.pskBinders) {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: invalid or missing PSK binders")
	}
	if len(hs.clientHello.pskIdentities) == 0 {
		return nil
	}

	for i, identity := range hs.clientHello.pskIdentities {
		if i >= maxClientPSKIdentities {
			break
		}

		plaintext, _ := c.decryptTicket(identity.label)
		if plaintext == nil {
			continue
		}
		sessionState := new(sessionStateTLS13)
		if ok := sessionState.unmarshal(plaintext); !ok {
			continue
		}

		createdAt := time.Unix(int64(sessionState.createdAt), 0)
		if c.config.time().Sub(createdAt) > maxSessionTicketLifetime {
			continue
		}

		// We don't check the obfuscated ticket age because it's affected by
		// clock skew and it's only a freshness signal useful for shrinking the
		// window for replay attacks, which don't affect us as we don't do 0-RTT.

		pskSuite := cipherSuiteTLS13ByID(sessionState.cipherSuite)
		if pskSuite == nil || pskSuite.hash != hs.suite.hash {
			continue
		}

		// PSK connections don't re-establish client certificates, but carry
		// them over in the session ticket. Ensure the presence of client certs
		// in the ticket is consistent with the configured requirements.
		sessionHasClientCerts := len(sessionState.certificate.Certificate) != 0
		needClientCerts := requiresClientCert(c.config.ClientAuth)
		if needClientCerts && !sessionHasClientCerts {
			continue
		}
		if sessionHasClientCerts && c.config.ClientAuth == NoClientCert {
			continue
		}

		psk := hs.suite.expandLabel(sessionState.resumptionSecret, "resumption",
			nil, hs.suite.hash.Size())
		hs.earlySecret = hs.suite.extract(psk, nil)
		binderKey := hs.suite.deriveSecret(hs.earlySecret, resumptionBinderLabel, nil)
		// Clone the transcript in case a HelloRetryRequest was recorded.
		transcript := cloneHash(hs.transcript, hs.suite.hash)
		if transcript == nil {
			c.sendAlert(alertInternalError)
			return errors.New("tls: internal error: failed to clone hash")
		}
		transcript.Write(hs.clientHello.marshalWithoutBinders())
		pskBinder := hs.suite.finishedHash(binderKey, transcript)
		if !hmac.Equal(hs.clientHello.pskBinders[i], pskBinder) {
			c.sendAlert(alertDecryptError)
			return errors.New("tls: invalid PSK binder")
		}

		c.didResume = true
		if err := c.processCertsFromClient(sessionState.certificate); err != nil {
			return err
		}

		hs.hello.selectedIdentityPresent = true
		hs.hello.selectedIdentity = uint16(i)
		hs.usingPSK = true
		return nil
	}

	return nil
}

// cloneHash uses the encoding.BinaryMarshaler and encoding.BinaryUnmarshaler
// interfaces implemented by standard library hashes to clone the state of in
// to a new instance of h. It returns nil if the operation fails.
func cloneHash(in hash.Hash, h crypto.Hash) hash.Hash {
	// Recreate the interface to avoid importing encoding.
	type binaryMarshaler interface {
		MarshalBinary() (data []byte, err error)
		UnmarshalBinary(data []byte) error
	}
	marshaler, ok := in.(binaryMarshaler)
	if !ok {
		return nil
	}
	state, err := marshaler.MarshalBinary()
	if err != nil {
		return nil
	}
	out := h.New()
	unmarshaler, ok := out.(binaryMarshaler)
	if !ok {
		return nil
	}
	if err := unmarshaler.UnmarshalBinary(state); err != nil {
		return nil
	}
	return out
}

func (hs *serverHandshakeStateTLS13) pickCertificate() error {
	c := hs.c

	// Only one of PSK and certificates are used at a time.
	if hs.usingPSK {
		return nil
	}

	// signature_algorithms is required in TLS 1.3. See RFC 8446, Section 4.2.3.
	if len(hs.clientHello.supportedSignatureAlgorithms) == 0 {
		return c.sendAlert(alertMissingExtension)
	}

	certificate, err := c.config.getCertificate(clientHelloInfo(hs.ctx, c, hs.clientHello))
	if err != nil {
		if err == errNoCertificates {
			c.sendAlert(alertUnrecognizedName)
		} else {
			c.sendAlert(alertInternalError)
		}
		return err
	}
	hs.sigAlg, err = selectSignatureScheme(c.vers, certificate, hs.clientHello.supportedSignatureAlgorithms)
	if err != nil {
		// getCertificate returned a certificate that is unsupported or
		// incompatible with the client's signature algorithms.
		c.sendAlert(alertHandshakeFailure)
		return err
	}
	hs.cert = certificate

	return nil
}

// sendDummyChangeCipherSpec sends a ChangeCipherSpec record for compatibility
// with middleboxes that didn't implement TLS correctly. See RFC 8446, Appendix D.4.
func (hs *serverHandshakeStateTLS13) sendDummyChangeCipherSpec() error {
	if hs.sentDummyCCS {
		return nil
	}
	hs.sentDummyCCS = true
	_, err := hs.c.writeRecord(recordTypeChangeCipherSpec, []byte{1})
	return err
}

func (hs *serverHandshakeStateTLS13) doHelloRetryRequest(selectedGroup CurveID) error {
	c := hs.c

	// The first ClientHello gets double-hashed into the transcript upon a
	// HelloRetryRequest. See RFC 8446, Section 4.4.1.
	hs.transcript.Write(hs.clientHello.marshal())
	chHash := hs.transcript.Sum(nil)
	hs.transcript.Reset()
	hs.transcript.Write([]byte{typeMessageHash, 0, 0, uint8(len(chHash))})
	hs.transcript.Write(chHash)

	helloRetryRequest := &serverHelloMsg{
		vers:              hs.hello.vers,
		random:            helloRetryRequestRandom,
		sessionId:         hs.hello.sessionId,
		cipherSuite:       hs.hello.cipherSuite,
		compressionMethod: hs.hello.compressionMethod,
		supportedVersion:  hs.hello.supportedVersion,
		selectedGroup:     selectedGroup,
	}

	hs.transcript.Write(helloRetryRequest.marshal())
	if _, err := c.writeRecord(recordTypeHandshake, helloRetryRequest.marshal()); err != nil {
		return err
	}
	if err := hs.sendDummyChangeCipherSpec(); err != nil {
		return err
	}

	msg, err := c.readHandshake()
	if err != nil {
		return err
	}

	clientHello, ok := msg.(*clientHelloMsg)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return unexpectedMessageError(clientHello, msg)
	}
	if len(clientHello.keyShares) != 1 || clientHello.keyShares[0].group != selectedGroup {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: client sent invalid key share in second ClientHello")
	}
	if clientHello.earlyData {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: client indicated early data in second ClientHello")
	}
	if illegalClientHelloChange(clientHello, hs.clientHello) {
		c.sendAlert(alertIllegalParameter)
		return errors.New("tls: client illegally modified second ClientHello")
	}

	hs.clientHello = clientHello

	return nil
}

// illegalClientHelloChange reports whether the two ClientHello messages are
// different, with the exception of the changes allowed before and after a
// HelloRetryRequest. See RFC 8446, Section 4.1.2.
func illegalClientHelloChange(ch, ch1 *clientHelloMsg) bool {
	if len(ch.supportedVersions) != len(ch1.supportedVersions) ||
		len(ch.cipherSuites) != len(ch1.cipherSuites) ||
		len(ch.supportedCurves) != len(ch1.supportedCurves) ||
		len(ch.supportedSignatureAlgorithms) != len(ch1.supportedSignatureAlgorithms) ||
		len(ch.supportedPoints) != len(ch1.supportedPoints) ||
		ch.ocspStapling != ch1.ocspStapling ||
		len(ch.alpnProtocols) != len(ch1.alpnProtocols) ||
		ch.scts != ch1.scts ||
		len(ch.serverName) != len(ch1.serverName) ||
		len(ch.supportedCompressions) != len(ch1.supportedCompressions) ||
		len(ch.sessionTicket) != len(ch1.sessionTicket) ||
		ch.ticketSupported != ch1.ticketSupported ||
		len(ch.secureRenegotiation) != len(ch1.secureRenegotiation) ||
		ch.earlyData != ch1.earlyData {
		return true
	}

	for i := range ch.supportedVersions {
		if ch.supportedVersions[i] != ch1.supportedVersions[i] {
			return true
		}
	}
	for i := range ch.cipherSuites {
		if ch.cipherSuites[i] != ch1.cipherSuites[i] {
			return true
		}
	}
	for i := range ch.supportedCurves {
		if ch.supportedCurves[i] != ch1.supportedCurves[i] {
			return true
		}
	}
	for i := range ch.supportedSignatureAlgorithms {
		if ch.supportedSignatureAlgorithms[i] != ch1.supportedSignatureAlgorithms[i] {
			return true
		}
	}
	for i := range ch.supportedPoints {
		if ch.supportedPoints[i] != ch1.supportedPoints[i] {
			return true
		}
	}
	for i := range ch.alpnProtocols {
		if ch.alpnProtocols[i] != ch1.alpnProtocols[i] {
			return true
		}
	}
	if !bytes.Equal(ch.serverName, ch1.serverName) ||
		!bytes.Equal(ch.supportedCompressions, ch1.supportedCompressions) ||
		!bytes.Equal(ch.sessionTicket, ch1.sessionTicket) ||
		!bytes.Equal(ch.secureRenegotiation, ch1.secureRenegotiation) {
		return true
	}
	
	// A new key share must be present, and it must not match the old one.
	if len(ch1.keyShares) != 1 || len(ch.keyShares) != 1 ||
		ch1.keyShares[0].group == ch.keyShares[0].group ||
		bytes.Equal(ch1.keyShares[0].data, ch.keyShares[0].data) {
		return true
	}

	// If a PSK was offered, the binders must have changed.
	if len(ch.pskIdentities) != len(ch1.pskIdentities) {
		return true
	}
	if len(ch.pskIdentities) > 0 && bytes.Equal(ch.pskBinders[0], ch1.pskBinders[0]) {
		return true
	}
	
	// If a cookie was received, it must be echoed.
	if len(ch1.cookie) == 0 && len(ch.cookie) > 0 {
		return true
	}

	return false
}

func (hs *serverHandshakeStateTLS13) sendServerFinished() error {
	c := hs.c
	finished := new(finishedMsg)
	finished.verifyData = c.finishedHash.serverSum(hs.masterSecret)
	if _, err := c.writeHandshakeMsg(finished.marshal()); err != nil {
		return err
	}
	hs.transcript.Write(finished.marshal())
	return nil
}

func (hs *serverHandshakeStateTLS13) readClientCertificate() error {
	c := hs.c

	// If we did not ask for a certificate, the client will not send one.
	if c.config.ClientAuth == NoClientCert {
		return nil
	}
	
	msg, err := c.readHandshake()
	if err != nil {
		return err
	}

	certMsg, ok := msg.(*certificateMsgTLS13)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return unexpectedMessageError(certMsg, msg)
	}

	if hs.usingPSK {
		if len(certMsg.certificate.Certificate) > 0 {
			c.sendAlert(alertUnexpectedMessage)
			return errors.New("tls: client sent certificate in PSK handshake")
		}
		// The client is not required to send a CertificateVerify message, but
		// if they do, we'll try to read it.
		// The client should send nothing here.
		if _, err := c.readHandshake(); err != io.EOF {
			return errors.New("tls: client sent unexpected handshake message")
		}
		return nil
	}

	hs.transcript.Write(certMsg.marshal())
	if err := c.processCertsFromClient(certMsg.certificate); err != nil {
		return err
	}

	// Client must send a CertificateVerify message. See RFC 8446, Section 4.4.3.
	msg, err = c.readHandshake()
	if err != nil {
		return err
	}
	certVerify, ok := msg.(*certificateVerifyMsg)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return unexpectedMessageError(certVerify, msg)
	}

	if err := verifyClientCertificate(c, hs.transcript, certVerify); err != nil {
		return err
	}

	hs.transcript.Write(certVerify.marshal())
	
	// If we waited until the client certificates to send session tickets, we
	// are ready to do it now.
	if err := hs.sendSessionTickets(); err != nil {
		return err
	}

	return nil
}

func (hs *serverHandshakeStateTLS13) readClientFinished() error {
	c := hs.c
	msg, err := c.readHandshake()
	if err != nil {
		return err
	}
	finished, ok := msg.(*finishedMsg)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return unexpectedMessageError(finished, msg)
	}
	if !hmac.Equal(finished.verifyData, c.finishedHash.clientSum(hs.masterSecret)) {
		c.sendAlert(alertDecryptError)
		return errors.New("tls: client's Finished message is invalid")
	}
	hs.transcript.Write(finished.marshal())
	if err := c.in.changeCipherSpec(c.trafficSecret); err != nil {
		return err
	}
	return nil
}

func (hs *serverHandshakeStateTLS13) sendSessionTickets() error {
	c := hs.c
	if c.config.SessionTicketsDisabled || hs.usingPSK {
		return nil
	}
	if !c.config.SessionTicketsDisabled && !hs.usingPSK {
		ticket := new(newSessionTicketMsg)
		ticket.lifetime = uint32(maxSessionTicketLifetime.Seconds())
		ticket.label = c.encryptTicket(&sessionStateTLS13{
			cipherSuite:        c.cipherSuite,
			masterSecret:       c.resumptionSecret,
			certificate:        c.peerCertificates,
			verifiedChains:     c.verifiedChains,
			ocspResponse:       c.ocspResponse,
			scts:               c.scts,
			receivedAt:         c.config.time(),
		})
		if _, err := c.writeHandshakeMsg(ticket.marshal()); err != nil {
			return err
		}
	}
	return nil
}
