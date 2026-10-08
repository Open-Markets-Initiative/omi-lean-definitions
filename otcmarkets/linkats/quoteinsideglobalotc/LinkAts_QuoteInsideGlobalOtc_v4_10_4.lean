import Wire

/-!
# OTC Markets Group  v4.10.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinkatsQuoteinsideglobalotcLinkV4104

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

/-- Security Message: 32 bytes -/
structure SecurityMessage where
  channelSeqNum : BitVec 32
  symbol : Alpha 10
  lastUpdateMilli : BitVec 64
  securityAction : BitVec 8
  assetClass : BitVec 8
  securityId : BitVec 32
  securityFlags : BitVec 8
  tier : BitVec 8
  reportingStatus : ReportingStatus
  securityStatus : SecurityStatus
  deriving DecidableEq, Repr

namespace SecurityMessage

def encode (message : SecurityMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.lastUpdateMilli
    ++ (encodeUInt 1 message.securityAction
    ++ (encodeUInt 1 message.assetClass
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUIntLE 1 message.securityFlags
    ++ (encodeUInt 1 message.tier
    ++ (ReportingStatus.encode message.reportingStatus
    ++ (SecurityStatus.encode message.securityStatus)))))))))

def decode (bytes : List UInt8) : Option (SecurityMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (lastUpdateMilli, bytes) ← decodeUInt 8 bytes
  let (securityAction, bytes) ← decodeUInt 1 bytes
  let (assetClass, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (securityFlags, bytes) ← decodeUIntLE 1 bytes
  let (tier, bytes) ← decodeUInt 1 bytes
  let (reportingStatus, bytes) ← ReportingStatus.decode bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  pure ({ channelSeqNum, symbol, lastUpdateMilli, securityAction, assetClass, securityId, securityFlags, tier, reportingStatus, securityStatus }, bytes)

@[simp] theorem encode_length (message : SecurityMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length, ReportingStatus.encode_length, SecurityStatus.encode_length]

theorem encode_length_pos (message : SecurityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ReportingStatus.decode_encode, some_bind]
  dsimp only
  rw [SecurityStatus.decode_encode, some_bind]
  rfl

end SecurityMessage

/-- Inside Message: 56 bytes -/
structure InsideMessage where
  channelSeqNum : BitVec 32
  insideId : BitVec 32
  insideAction : BitVec 8
  quoteFlags : BitVec 8
  securityId : BitVec 32
  askPrice : BitVec 64
  askSize : BitVec 32
  askTimeMilli : BitVec 64
  bidPrice : BitVec 64
  bidSize : BitVec 32
  bidTimeMilli : BitVec 64
  askNumPricedMp : BitVec 8
  bidNumPricedMp : BitVec 8
  deriving DecidableEq, Repr

namespace InsideMessage

def encode (message : InsideMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 4 message.insideId
    ++ (encodeUInt 1 message.insideAction
    ++ (encodeUIntLE 1 message.quoteFlags
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUInt 8 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (encodeUInt 8 message.askTimeMilli
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.bidTimeMilli
    ++ (encodeUInt 1 message.askNumPricedMp
    ++ (encodeUInt 1 message.bidNumPricedMp))))))))))))

def decode (bytes : List UInt8) : Option (InsideMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (insideId, bytes) ← decodeUInt 4 bytes
  let (insideAction, bytes) ← decodeUInt 1 bytes
  let (quoteFlags, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 8 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (askTimeMilli, bytes) ← decodeUInt 8 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (bidTimeMilli, bytes) ← decodeUInt 8 bytes
  let (askNumPricedMp, bytes) ← decodeUInt 1 bytes
  let (bidNumPricedMp, bytes) ← decodeUInt 1 bytes
  pure ({ channelSeqNum, insideId, insideAction, quoteFlags, securityId, askPrice, askSize, askTimeMilli, bidPrice, bidSize, bidTimeMilli, askNumPricedMp, bidNumPricedMp }, bytes)

@[simp] theorem encode_length (message : InsideMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : InsideMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InsideMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InsideMessage

/-- Inside Update Message: 30 bytes -/
structure InsideUpdateMessage where
  channelSeqNum : BitVec 32
  insideId : BitVec 32
  quoteFlags : BitVec 8
  price : BitVec 64
  size : BitVec 32
  insideTimeMilli : BitVec 64
  numPricedMp : BitVec 8
  deriving DecidableEq, Repr

namespace InsideUpdateMessage

def encode (message : InsideUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 4 message.insideId
    ++ (encodeUIntLE 1 message.quoteFlags
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.size
    ++ (encodeUInt 8 message.insideTimeMilli
    ++ (encodeUInt 1 message.numPricedMp))))))

def decode (bytes : List UInt8) : Option (InsideUpdateMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (insideId, bytes) ← decodeUInt 4 bytes
  let (quoteFlags, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (insideTimeMilli, bytes) ← decodeUInt 8 bytes
  let (numPricedMp, bytes) ← decodeUInt 1 bytes
  pure ({ channelSeqNum, insideId, quoteFlags, price, size, insideTimeMilli, numPricedMp }, bytes)

@[simp] theorem encode_length (message : InsideUpdateMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : InsideUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InsideUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InsideUpdateMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | startOfSpinMessage (message : StartOfSpinMessage) -- 11
  | endOfSpinMessage (message : EndOfSpinMessage) -- 12
  | marketOpenMessage (message : MarketOpenMessage) -- 13
  | marketCloseMessage (message : MarketCloseMessage) -- 14
  | securityMessage (message : SecurityMessage) -- 9
  | insideMessage (message : InsideMessage) -- 3
  | insideUpdateMessage (message : InsideUpdateMessage) -- 4
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .startOfSpinMessage _ => 11
  | .endOfSpinMessage _ => 12
  | .marketOpenMessage _ => 13
  | .marketCloseMessage _ => 14
  | .securityMessage _ => 9
  | .insideMessage _ => 3
  | .insideUpdateMessage _ => 4

def encode : Payload → List UInt8
  | .startOfSpinMessage message => StartOfSpinMessage.encode message
  | .endOfSpinMessage message => EndOfSpinMessage.encode message
  | .marketOpenMessage message => MarketOpenMessage.encode message
  | .marketCloseMessage message => MarketCloseMessage.encode message
  | .securityMessage message => SecurityMessage.encode message
  | .insideMessage message => InsideMessage.encode message
  | .insideUpdateMessage message => InsideUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 56 := by
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
  | securityMessage inner =>
    simp only [encode, SecurityMessage.encode_length]
    omega
  | insideMessage inner =>
    simp only [encode, InsideMessage.encode_length]
    omega
  | insideUpdateMessage inner =>
    simp only [encode, InsideUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 11 then (StartOfSpinMessage.decode bytes).map fun (message, rest) => (.startOfSpinMessage message, rest)
  else if tag = 12 then (EndOfSpinMessage.decode bytes).map fun (message, rest) => (.endOfSpinMessage message, rest)
  else if tag = 13 then (MarketOpenMessage.decode bytes).map fun (message, rest) => (.marketOpenMessage message, rest)
  else if tag = 14 then (MarketCloseMessage.decode bytes).map fun (message, rest) => (.marketCloseMessage message, rest)
  else if tag = 9 then (SecurityMessage.decode bytes).map fun (message, rest) => (.securityMessage message, rest)
  else if tag = 3 then (InsideMessage.decode bytes).map fun (message, rest) => (.insideMessage message, rest)
  else if tag = 4 then (InsideUpdateMessage.decode bytes).map fun (message, rest) => (.insideUpdateMessage message, rest)
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
  | securityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityMessage.encode_length]
    omega
  | insideMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InsideMessage.encode_length]
    omega
  | insideUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InsideUpdateMessage.encode_length]
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

end Omi.OtcmarketsLinkatsQuoteinsideglobalotcLinkV4104
