import Wire

/-!
# OTC Markets Group  v4.10.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Flag is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: a Heartbeat of 1 marks Heartbeat Packet and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Extended Security Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinkatsReferencedatanocusipLinkV4104

/-- Reporting Status: one byte code -/
def ReportingStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x47, 0x49, 0x4E, 0x4F, 0x52, 0x56, 0x57]

inductive ReportingStatus where
  | alternativeReporting -- Alternative Reporting
  | bankThrift -- Bank Thrift
  | secReportingRegCf -- Sec Reporting Reg Cf
  | secReporting -- Sec Reporting
  | internationalReporting -- International Reporting
  | insuranceCompany -- Insurance Company
  | noReporting -- No Reporting
  | otherReporting -- Other Reporting
  | finraReporting -- Finra Reporting
  | secInvestmentCompany -- Sec Investment Company
  | secReportingRegA -- Sec Reporting Reg A
  | unlisted (byte : { byte : UInt8 // byte ∉ ReportingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReportingStatus

def toByte : ReportingStatus → UInt8
  | .alternativeReporting => 0x41
  | .bankThrift => 0x42
  | .secReportingRegCf => 0x43
  | .secReporting => 0x46
  | .internationalReporting => 0x47
  | .insuranceCompany => 0x49
  | .noReporting => 0x4E
  | .otherReporting => 0x4F
  | .finraReporting => 0x52
  | .secInvestmentCompany => 0x56
  | .secReportingRegA => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReportingStatus :=
  if byte = 0x41 then .alternativeReporting
  else if byte = 0x42 then .bankThrift
  else if byte = 0x43 then .secReportingRegCf
  else if byte = 0x46 then .secReporting
  else if byte = 0x47 then .internationalReporting
  else if byte = 0x49 then .insuranceCompany
  else if byte = 0x4E then .noReporting
  else if byte = 0x4F then .otherReporting
  else if byte = 0x52 then .finraReporting
  else if byte = 0x56 then .secInvestmentCompany
  else .secReportingRegA

def ofByte (byte : UInt8) : ReportingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReportingStatus) : ofByte value.toByte = value := by
  cases value with
  | alternativeReporting => decide
  | bankThrift => decide
  | secReportingRegCf => decide
  | secReporting => decide
  | internationalReporting => decide
  | insuranceCompany => decide
  | noReporting => decide
  | otherReporting => decide
  | finraReporting => decide
  | secInvestmentCompany => decide
  | secReportingRegA => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReportingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReportingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReportingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReportingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReportingStatus

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x41, 0x51, 0x53, 0x48, 0x49, 0x52, 0x44]

inductive SecurityStatus where
  | active -- Active
  | quoteOnly -- Quote Only
  | suspended -- Suspended
  | halted -- Halted
  | internalHalt -- Internal Halt
  | revoked -- Revoked
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .active => 0x41
  | .quoteOnly => 0x51
  | .suspended => 0x53
  | .halted => 0x48
  | .internalHalt => 0x49
  | .revoked => 0x52
  | .deleted => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x41 then .active
  else if byte = 0x51 then .quoteOnly
  else if byte = 0x53 then .suspended
  else if byte = 0x48 then .halted
  else if byte = 0x49 then .internalHalt
  else if byte = 0x52 then .revoked
  else .deleted

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | quoteOnly => decide
  | suspended => decide
  | halted => decide
  | internalHalt => decide
  | revoked => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Start Of Spin Message: 17 bytes -/
structure StartOfSpinMessage where
  channelSeqNum : BitVec 32
  spinType : BitVec 8
  spinStartTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace StartOfSpinMessage

def encode (message : StartOfSpinMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 1 message.spinType
    ++ (encodeUInt 8 message.spinStartTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum)))

def decode (bytes : List UInt8) : Option (StartOfSpinMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinStartTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, spinType, spinStartTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : StartOfSpinMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StartOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSpinMessage

/-- End Of Spin Message: 21 bytes -/
structure EndOfSpinMessage where
  channelSeqNum : BitVec 32
  spinType : BitVec 8
  spinMsgCt : BitVec 32
  spinEndTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfSpinMessage

def encode (message : EndOfSpinMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 1 message.spinType
    ++ (encodeUInt 4 message.spinMsgCt
    ++ (encodeUInt 8 message.spinEndTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum))))

def decode (bytes : List UInt8) : Option (EndOfSpinMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinMsgCt, bytes) ← decodeUInt 4 bytes
  let (spinEndTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, spinType, spinMsgCt, spinEndTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : EndOfSpinMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EndOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfSpinMessage

/-- Market Open Message: 20 bytes -/
structure MarketOpenMessage where
  channelSeqNum : BitVec 32
  marketOpen : BitVec 64
  marketClose : BitVec 64
  deriving DecidableEq, Repr

namespace MarketOpenMessage

def encode (message : MarketOpenMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 8 message.marketOpen
    ++ (encodeUInt 8 message.marketClose))

def decode (bytes : List UInt8) : Option (MarketOpenMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (marketOpen, bytes) ← decodeUInt 8 bytes
  let (marketClose, bytes) ← decodeUInt 8 bytes
  pure ({ channelSeqNum, marketOpen, marketClose }, bytes)

@[simp] theorem encode_length (message : MarketOpenMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketOpenMessage

/-- Market Close Message: 16 bytes -/
structure MarketCloseMessage where
  channelSeqNum : BitVec 32
  marketCloseTimeMilli : BitVec 64
  marketMsgCt : BitVec 32
  deriving DecidableEq, Repr

namespace MarketCloseMessage

def encode (message : MarketCloseMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 8 message.marketCloseTimeMilli
    ++ (encodeUInt 4 message.marketMsgCt))

def decode (bytes : List UInt8) : Option (MarketCloseMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (marketCloseTimeMilli, bytes) ← decodeUInt 8 bytes
  let (marketMsgCt, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, marketCloseTimeMilli, marketMsgCt }, bytes)

@[simp] theorem encode_length (message : MarketCloseMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketCloseMessage

/-- Security Detail -/
structure SecurityDetail where
  securityDetailName : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace SecurityDetail

def encode (message : SecurityDetail) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDetailName.val.length)
    ++ (encodeMany Byte.encode message.securityDetailName.val)

def decode (bytes : List UInt8) : Option (SecurityDetail × List UInt8) := do
  let (securityDetailSize, bytes) ← decodeUInt 1 bytes
  let (securityDetailName_, bytes) ← decodeMany Byte.decode securityDetailSize.toNat bytes
  if fits_securityDetailName : securityDetailName_.length < 256 ^ 1 then
    pure ({ securityDetailName := ⟨securityDetailName_, fits_securityDetailName⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDetail) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDetail) : (encode message).length ≤ 256 := by
  have bound_securityDetailName := message.securityDetailName.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDetail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDetailName.length_lt]
  rfl

end SecurityDetail

/-- Issuer -/
structure Issuer where
  issuerName : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Issuer

def encode (message : Issuer) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.issuerName.val.length)
    ++ (encodeMany Byte.encode message.issuerName.val)

def decode (bytes : List UInt8) : Option (Issuer × List UInt8) := do
  let (issuerSize, bytes) ← decodeUInt 1 bytes
  let (issuerName_, bytes) ← decodeMany Byte.decode issuerSize.toNat bytes
  if fits_issuerName : issuerName_.length < 256 ^ 1 then
    pure ({ issuerName := ⟨issuerName_, fits_issuerName⟩ }, bytes)
  else none

theorem encode_length_pos (message : Issuer) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Issuer) : (encode message).length ≤ 256 := by
  have bound_issuerName := message.issuerName.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Issuer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.issuerName.length_lt]
  rfl

end Issuer

/-- Extended Security No Cusip Message -/
structure ExtendedSecurityNoCusipMessage where
  channelSeqNum : BitVec 32
  symbol : Alpha 10
  lastUpdateMilli : BitVec 64
  securityAction : BitVec 8
  otcIssuerId : BitVec 32
  securityDesc : Alpha 25
  shortName : Alpha 25
  assetClass : BitVec 8
  securityType : Alpha 5
  primaryMarket : Alpha 3
  securityId : BitVec 32
  extendedSecurityFlags : BitVec 16
  tier : BitVec 8
  reportingStatus : ReportingStatus
  disclosureStatus : BitVec 8
  securityStatus : SecurityStatus
  parValue : BitVec 64
  coupon : BitVec 64
  maturityDateMilli : BitVec 64
  callableDateMilli : BitVec 64
  adrRatio : BitVec 64
  adrLevel : Alpha 15
  securityDetail : SecurityDetail
  issuer : Issuer
  deriving DecidableEq, Repr

namespace ExtendedSecurityNoCusipMessage

def encode (message : ExtendedSecurityNoCusipMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.lastUpdateMilli
    ++ (encodeUInt 1 message.securityAction
    ++ (encodeUInt 4 message.otcIssuerId
    ++ (Alpha.encode message.securityDesc
    ++ (Alpha.encode message.shortName
    ++ (encodeUInt 1 message.assetClass
    ++ (Alpha.encode message.securityType
    ++ (Alpha.encode message.primaryMarket
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUInt 2 message.extendedSecurityFlags
    ++ (encodeUInt 1 message.tier
    ++ (ReportingStatus.encode message.reportingStatus
    ++ (encodeUInt 1 message.disclosureStatus
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUInt 8 message.parValue
    ++ (encodeUInt 8 message.coupon
    ++ (encodeUInt 8 message.maturityDateMilli
    ++ (encodeUInt 8 message.callableDateMilli
    ++ (encodeUInt 8 message.adrRatio
    ++ (Alpha.encode message.adrLevel
    ++ (SecurityDetail.encode message.securityDetail
    ++ (Issuer.encode message.issuer)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExtendedSecurityNoCusipMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (lastUpdateMilli, bytes) ← decodeUInt 8 bytes
  let (securityAction, bytes) ← decodeUInt 1 bytes
  let (otcIssuerId, bytes) ← decodeUInt 4 bytes
  let (securityDesc, bytes) ← Alpha.decode 25 bytes
  let (shortName, bytes) ← Alpha.decode 25 bytes
  let (assetClass, bytes) ← decodeUInt 1 bytes
  let (securityType, bytes) ← Alpha.decode 5 bytes
  let (primaryMarket, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (extendedSecurityFlags, bytes) ← decodeUInt 2 bytes
  let (tier, bytes) ← decodeUInt 1 bytes
  let (reportingStatus, bytes) ← ReportingStatus.decode bytes
  let (disclosureStatus, bytes) ← decodeUInt 1 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (parValue, bytes) ← decodeUInt 8 bytes
  let (coupon, bytes) ← decodeUInt 8 bytes
  let (maturityDateMilli, bytes) ← decodeUInt 8 bytes
  let (callableDateMilli, bytes) ← decodeUInt 8 bytes
  let (adrRatio, bytes) ← decodeUInt 8 bytes
  let (adrLevel, bytes) ← Alpha.decode 15 bytes
  let (securityDetail, bytes) ← SecurityDetail.decode bytes
  let (issuer, bytes) ← Issuer.decode bytes
  pure ({ channelSeqNum, symbol, lastUpdateMilli, securityAction, otcIssuerId, securityDesc, shortName, assetClass, securityType, primaryMarket, securityId, extendedSecurityFlags, tier, reportingStatus, disclosureStatus, securityStatus, parValue, coupon, maturityDateMilli, callableDateMilli, adrRatio, adrLevel, securityDetail, issuer }, bytes)

theorem encode_length_pos (message : ExtendedSecurityNoCusipMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExtendedSecurityNoCusipMessage) : (encode message).length ≤ 663 := by
  have bound_securityDetail := SecurityDetail.encode_length_le message.securityDetail
  have bound_issuer := Issuer.encode_length_le message.issuer
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ReportingStatus.encode_length, SecurityStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExtendedSecurityNoCusipMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ReportingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDetail.decode_encode, some_bind]
  dsimp only
  rw [Issuer.decode_encode, some_bind]
  rfl

end ExtendedSecurityNoCusipMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | startOfSpinMessage (message : StartOfSpinMessage) -- 11
  | endOfSpinMessage (message : EndOfSpinMessage) -- 12
  | marketOpenMessage (message : MarketOpenMessage) -- 13
  | marketCloseMessage (message : MarketCloseMessage) -- 14
  | extendedSecurityNoCusipMessage (message : ExtendedSecurityNoCusipMessage) -- 16
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .startOfSpinMessage _ => 11
  | .endOfSpinMessage _ => 12
  | .marketOpenMessage _ => 13
  | .marketCloseMessage _ => 14
  | .extendedSecurityNoCusipMessage _ => 16

def encode : Payload → List UInt8
  | .startOfSpinMessage message => StartOfSpinMessage.encode message
  | .endOfSpinMessage message => EndOfSpinMessage.encode message
  | .marketOpenMessage message => MarketOpenMessage.encode message
  | .marketCloseMessage message => MarketCloseMessage.encode message
  | .extendedSecurityNoCusipMessage message => ExtendedSecurityNoCusipMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 663 := by
  cases message with
  | startOfSpinMessage inner =>
    simp only [encode, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [encode, EndOfSpinMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [encode, MarketOpenMessage.encode_length]
    omega
  | marketCloseMessage inner =>
    simp only [encode, MarketCloseMessage.encode_length]
    omega
  | extendedSecurityNoCusipMessage inner =>
    have bound_inner := ExtendedSecurityNoCusipMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 11 then (StartOfSpinMessage.decode bytes).map fun (message, rest) => (.startOfSpinMessage message, rest)
  else if tag = 12 then (EndOfSpinMessage.decode bytes).map fun (message, rest) => (.endOfSpinMessage message, rest)
  else if tag = 13 then (MarketOpenMessage.decode bytes).map fun (message, rest) => (.marketOpenMessage message, rest)
  else if tag = 14 then (MarketCloseMessage.decode bytes).map fun (message, rest) => (.marketCloseMessage message, rest)
  else if tag = 16 then (ExtendedSecurityNoCusipMessage.decode bytes).map fun (message, rest) => (.extendedSecurityNoCusipMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | startOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfSpinMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOpenMessage.encode_length]
    omega
  | marketCloseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketCloseMessage.encode_length]
    omega
  | extendedSecurityNoCusipMessage inner =>
    have bound_inner := ExtendedSecurityNoCusipMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  seqNum : BitVec 32
  packetFlag : BitVec 8
  packetMilli : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetSize
    ++ (encodeUInt 4 message.seqNum
    ++ (encodeUIntLE 1 message.packetFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 4 message.packetMilli
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUInt 2 bytes
  let (seqNum, bytes) ← decodeUInt 4 bytes
  let (packetFlag, bytes) ← decodeUIntLE 1 bytes
  let (messages, bytes) ← decodeUInt 1 bytes
  let (packetMilli, bytes) ← decodeUInt 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messages.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, seqNum, packetFlag, packetMilli, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.OtcmarketsLinkatsReferencedatanocusipLinkV4104
