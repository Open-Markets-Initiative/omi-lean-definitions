import Wire

/-!
# OTC Markets Group OTC Retransmission v1.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Security Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinknqbRetransmissionLinkV118

/-- Reporting Status: one byte code -/
def ReportingStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x47, 0x49, 0x4E, 0x4F, 0x52, 0x56, 0x57]

inductive ReportingStatus where
  | alternativeReportingStandard -- Alternative Reporting Standard
  | bankThrift -- Bank Thrift
  | secReporting -- Sec Reporting
  | internationalReporting -- International Reporting
  | insuranceCompany -- Insurance Company
  | noReporting -- No Reporting
  | otherReportingStandard -- Other Reporting Standard
  | finraReporting -- Finra Reporting
  | secReportingInvestmentCompany -- Sec Reporting Investment Company
  | secReportingRegA -- Sec Reporting Reg A
  | unlisted (byte : { byte : UInt8 // byte ∉ ReportingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReportingStatus

def toByte : ReportingStatus → UInt8
  | .alternativeReportingStandard => 0x41
  | .bankThrift => 0x42
  | .secReporting => 0x46
  | .internationalReporting => 0x47
  | .insuranceCompany => 0x49
  | .noReporting => 0x4E
  | .otherReportingStandard => 0x4F
  | .finraReporting => 0x52
  | .secReportingInvestmentCompany => 0x56
  | .secReportingRegA => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReportingStatus :=
  if byte = 0x41 then .alternativeReportingStandard
  else if byte = 0x42 then .bankThrift
  else if byte = 0x46 then .secReporting
  else if byte = 0x47 then .internationalReporting
  else if byte = 0x49 then .insuranceCompany
  else if byte = 0x4E then .noReporting
  else if byte = 0x4F then .otherReportingStandard
  else if byte = 0x52 then .finraReporting
  else if byte = 0x56 then .secReportingInvestmentCompany
  else .secReportingRegA

def ofByte (byte : UInt8) : ReportingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReportingStatus) : ofByte value.toByte = value := by
  cases value with
  | alternativeReportingStandard => decide
  | bankThrift => decide
  | secReporting => decide
  | internationalReporting => decide
  | insuranceCompany => decide
  | noReporting => decide
  | otherReportingStandard => decide
  | finraReporting => decide
  | secReportingInvestmentCompany => decide
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
  [0x41, 0x51, 0x53, 0x48, 0x49, 0x52, 0x44, 0x58]

inductive SecurityStatus where
  | active -- Active
  | quoteOnly -- Quote Only
  | suspended -- Suspended
  | halted -- Halted
  | internalHalt -- Internal Halt
  | revoked -- Revoked
  | deleted -- Deleted
  | removedFromIdqs -- Removed From Idqs
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
  | .removedFromIdqs => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x41 then .active
  else if byte = 0x51 then .quoteOnly
  else if byte = 0x53 then .suspended
  else if byte = 0x48 then .halted
  else if byte = 0x49 then .internalHalt
  else if byte = 0x52 then .revoked
  else if byte = 0x44 then .deleted
  else .removedFromIdqs

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
  | removedFromIdqs => decide
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

/-- Side Indicator: one byte code -/
def SideIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive SideIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ SideIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideIndicator

def toByte : SideIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : SideIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideIndicator

/-- Unsolicited: one byte code -/
def Unsolicited.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Unsolicited where
  | unsolicited -- Unsolicited
  | notUnsolicited -- Not Unsolicited
  | unlisted (byte : { byte : UInt8 // byte ∉ Unsolicited.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Unsolicited

def toByte : Unsolicited → UInt8
  | .unsolicited => 0x59
  | .notUnsolicited => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Unsolicited :=
  if byte = 0x59 then .unsolicited
  else .notUnsolicited

def ofByte (byte : UInt8) : Unsolicited :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Unsolicited) : ofByte value.toByte = value := by
  cases value with
  | unsolicited => decide
  | notUnsolicited => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Unsolicited) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Unsolicited × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Unsolicited) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Unsolicited) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Unsolicited

/-- Current Inside Imbalance Side: one byte code -/
def CurrentInsideImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x4E, 0x4F]

inductive CurrentInsideImbalanceSide where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | noImbalance -- No Imbalance
  | noMarketableOrders -- No Marketable Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentInsideImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentInsideImbalanceSide

def toByte : CurrentInsideImbalanceSide → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .noImbalance => 0x4E
  | .noMarketableOrders => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentInsideImbalanceSide :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else if byte = 0x4E then .noImbalance
  else .noMarketableOrders

def ofByte (byte : UInt8) : CurrentInsideImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentInsideImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | noImbalance => decide
  | noMarketableOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentInsideImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentInsideImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentInsideImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentInsideImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentInsideImbalanceSide

/-- Moc Shares Unmatched: one byte code -/
def MocSharesUnmatched.codes : List UInt8 :=
  [0x42, 0x53, 0x4F]

inductive MocSharesUnmatched where
  | buyMocNotMatched -- Buy Moc Not Matched
  | sellMocNotMatched -- Sell Moc Not Matched
  | noMocUnmatched -- No Moc Unmatched
  | unlisted (byte : { byte : UInt8 // byte ∉ MocSharesUnmatched.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocSharesUnmatched

def toByte : MocSharesUnmatched → UInt8
  | .buyMocNotMatched => 0x42
  | .sellMocNotMatched => 0x53
  | .noMocUnmatched => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MocSharesUnmatched :=
  if byte = 0x42 then .buyMocNotMatched
  else if byte = 0x53 then .sellMocNotMatched
  else .noMocUnmatched

def ofByte (byte : UInt8) : MocSharesUnmatched :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocSharesUnmatched) : ofByte value.toByte = value := by
  cases value with
  | buyMocNotMatched => decide
  | sellMocNotMatched => decide
  | noMocUnmatched => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MocSharesUnmatched) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MocSharesUnmatched × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MocSharesUnmatched) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MocSharesUnmatched) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MocSharesUnmatched

/-- Start Of Spin Message: 13 bytes -/
structure StartOfSpinMessage where
  spinType : BitVec 8
  spinStartTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace StartOfSpinMessage

def encode (message : StartOfSpinMessage) : List UInt8 :=
  encodeUInt 1 message.spinType
    ++ (encodeUInt 8 message.spinStartTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum))

def decode (bytes : List UInt8) : Option (StartOfSpinMessage × List UInt8) := do
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinStartTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ spinType, spinStartTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : StartOfSpinMessage) : (encode message).length = 13 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSpinMessage

/-- End Of Spin Message: 17 bytes -/
structure EndOfSpinMessage where
  spinType : BitVec 8
  spinMsgCt : BitVec 32
  spinEndTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfSpinMessage

def encode (message : EndOfSpinMessage) : List UInt8 :=
  encodeUInt 1 message.spinType
    ++ (encodeUInt 4 message.spinMsgCt
    ++ (encodeUInt 8 message.spinEndTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum)))

def decode (bytes : List UInt8) : Option (EndOfSpinMessage × List UInt8) := do
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinMsgCt, bytes) ← decodeUInt 4 bytes
  let (spinEndTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ spinType, spinMsgCt, spinEndTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : EndOfSpinMessage) : (encode message).length = 17 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfSpinMessage

/-- Trading Session Message: 9 bytes -/
structure TradingSessionMessage where
  sessionTime : BitVec 64
  tradingSession : BitVec 8
  deriving DecidableEq, Repr

namespace TradingSessionMessage

def encode (message : TradingSessionMessage) : List UInt8 :=
  encodeUInt 8 message.sessionTime
    ++ (encodeUInt 1 message.tradingSession)

def decode (bytes : List UInt8) : Option (TradingSessionMessage × List UInt8) := do
  let (sessionTime, bytes) ← decodeUInt 8 bytes
  let (tradingSession, bytes) ← decodeUInt 1 bytes
  pure ({ sessionTime, tradingSession }, bytes)

@[simp] theorem encode_length (message : TradingSessionMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradingSessionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingSessionMessage

/-- Security Message: 33 bytes -/
structure SecurityMessage where
  symbol : Alpha 14
  lastUpdateMilli : BitVec 64
  securityAction : BitVec 8
  assetClass : BitVec 8
  securityId : BitVec 32
  securityFlags : BitVec 16
  tier : BitVec 8
  reportingStatus : ReportingStatus
  securityStatus : SecurityStatus
  deriving DecidableEq, Repr

namespace SecurityMessage

def encode (message : SecurityMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUInt 8 message.lastUpdateMilli
    ++ (encodeUInt 1 message.securityAction
    ++ (encodeUInt 1 message.assetClass
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUInt 2 message.securityFlags
    ++ (encodeUInt 1 message.tier
    ++ (ReportingStatus.encode message.reportingStatus
    ++ (SecurityStatus.encode message.securityStatus))))))))

def decode (bytes : List UInt8) : Option (SecurityMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (lastUpdateMilli, bytes) ← decodeUInt 8 bytes
  let (securityAction, bytes) ← decodeUInt 1 bytes
  let (assetClass, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (securityFlags, bytes) ← decodeUInt 2 bytes
  let (tier, bytes) ← decodeUInt 1 bytes
  let (reportingStatus, bytes) ← ReportingStatus.decode bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  pure ({ symbol, lastUpdateMilli, securityAction, assetClass, securityId, securityFlags, tier, reportingStatus, securityStatus }, bytes)

@[simp] theorem encode_length (message : SecurityMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ReportingStatus.encode_length, SecurityStatus.encode_length]

theorem encode_length_pos (message : SecurityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ReportingStatus.decode_encode, some_bind]
  dsimp only
  rw [SecurityStatus.decode_encode, some_bind]
  rfl

end SecurityMessage

/-- Order Add Message: 52 bytes -/
structure OrderAddMessage where
  time : BitVec 32
  orderId : Alpha 14
  sideIndicator : SideIndicator
  quantity : BitVec 32
  symbol : Alpha 14
  price : BitVec 64
  firmId : Alpha 4
  unsolicited : Unsolicited
  orderFlags : BitVec 16
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.orderId
    ++ (SideIndicator.encode message.sideIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.firmId
    ++ (Unsolicited.encode message.unsolicited
    ++ (encodeUInt 2 message.orderFlags))))))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← Alpha.decode 14 bytes
  let (sideIndicator, bytes) ← SideIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (unsolicited_, bytes) ← Unsolicited.decode bytes
  let (orderFlags, bytes) ← decodeUInt 2 bytes
  pure ({ time, orderId, sideIndicator, quantity, symbol, price, firmId, unsolicited := unsolicited_, orderFlags }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SideIndicator.encode_length, Unsolicited.encode_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SideIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Unsolicited.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderAddMessage

/-- Order Update Message: 32 bytes -/
structure OrderUpdateMessage where
  time : BitVec 32
  orderId : Alpha 14
  quantity : BitVec 32
  price : BitVec 64
  orderFlags : BitVec 16
  deriving DecidableEq, Repr

namespace OrderUpdateMessage

def encode (message : OrderUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.orderId
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 2 message.orderFlags))))

def decode (bytes : List UInt8) : Option (OrderUpdateMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← Alpha.decode 14 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderFlags, bytes) ← decodeUInt 2 bytes
  pure ({ time, orderId, quantity, price, orderFlags }, bytes)

@[simp] theorem encode_length (message : OrderUpdateMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderUpdateMessage

/-- Order Delete Message: 18 bytes -/
structure OrderDeleteMessage where
  time : BitVec 32
  orderId : Alpha 14
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.orderId)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← Alpha.decode 14 bytes
  pure ({ time, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Execution Message: 34 bytes -/
structure OrderExecutionMessage where
  time : BitVec 32
  orderId : Alpha 14
  executedQuantity : BitVec 32
  remainingQuantity : BitVec 32
  executionId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutionMessage

def encode (message : OrderExecutionMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.orderId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.remainingQuantity
    ++ (encodeUInt 8 message.executionId))))

def decode (bytes : List UInt8) : Option (OrderExecutionMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← Alpha.decode 14 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (remainingQuantity, bytes) ← decodeUInt 4 bytes
  let (executionId, bytes) ← decodeUInt 8 bytes
  pure ({ time, orderId, executedQuantity, remainingQuantity, executionId }, bytes)

@[simp] theorem encode_length (message : OrderExecutionMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutionMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutionMessage

/-- Order Execution With Price Message: 42 bytes -/
structure OrderExecutionWithPriceMessage where
  time : BitVec 32
  orderId : Alpha 14
  executedQuantity : BitVec 32
  remainingQuantity : BitVec 32
  executionId : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutionWithPriceMessage

def encode (message : OrderExecutionWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.orderId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.remainingQuantity
    ++ (encodeUInt 8 message.executionId
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (OrderExecutionWithPriceMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← Alpha.decode 14 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (remainingQuantity, bytes) ← decodeUInt 4 bytes
  let (executionId, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ time, orderId, executedQuantity, remainingQuantity, executionId, price }, bytes)

@[simp] theorem encode_length (message : OrderExecutionWithPriceMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutionWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutionWithPriceMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutionWithPriceMessage

/-- Trade Message: 47 bytes -/
structure TradeMessage where
  time : BitVec 32
  sideIndicator : SideIndicator
  quantity : BitVec 32
  symbol : Alpha 14
  price : BitVec 64
  executionId : BitVec 64
  reservedBinaryLong8 : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (SideIndicator.encode message.sideIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.executionId
    ++ (encodeUInt 8 message.reservedBinaryLong8))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (sideIndicator, bytes) ← SideIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (executionId, bytes) ← decodeUInt 8 bytes
  let (reservedBinaryLong8, bytes) ← decodeUInt 8 bytes
  pure ({ time, sideIndicator, quantity, symbol, price, executionId, reservedBinaryLong8 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SideIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMessage

/-- Top Of Book Message: 43 bytes -/
structure TopOfBookMessage where
  time : BitVec 32
  symbol : Alpha 14
  askPrice : BitVec 64
  askVolume : BitVec 32
  bidPrice : BitVec 64
  bidVolume : BitVec 32
  unsolicited : Unsolicited
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.askPrice
    ++ (encodeUInt 4 message.askVolume
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidVolume
    ++ (Unsolicited.encode message.unsolicited))))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (askPrice, bytes) ← decodeUInt 8 bytes
  let (askVolume, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidVolume, bytes) ← decodeUInt 4 bytes
  let (unsolicited_, bytes) ← Unsolicited.decode bytes
  pure ({ time, symbol, askPrice, askVolume, bidPrice, bidVolume, unsolicited := unsolicited_ }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Unsolicited.encode_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
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
  rw [Unsolicited.decode_encode, some_bind]
  rfl

end TopOfBookMessage

/-- Imbalance Message: 52 bytes -/
structure ImbalanceMessage where
  time : BitVec 32
  symbol : Alpha 14
  currentInsidePairedShares : BitVec 32
  currentInsideClosingPrice : BitVec 64
  currentInsideImbalanceQuantity : BitVec 32
  currentInsideImbalanceSide : CurrentInsideImbalanceSide
  fullClosingPrice : BitVec 64
  ocioOnlyClosingPrice : BitVec 64
  mocSharesUnmatched : MocSharesUnmatched
  deriving DecidableEq, Repr

namespace ImbalanceMessage

def encode (message : ImbalanceMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.currentInsidePairedShares
    ++ (encodeUInt 8 message.currentInsideClosingPrice
    ++ (encodeUInt 4 message.currentInsideImbalanceQuantity
    ++ (CurrentInsideImbalanceSide.encode message.currentInsideImbalanceSide
    ++ (encodeUInt 8 message.fullClosingPrice
    ++ (encodeUInt 8 message.ocioOnlyClosingPrice
    ++ (MocSharesUnmatched.encode message.mocSharesUnmatched))))))))

def decode (bytes : List UInt8) : Option (ImbalanceMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (currentInsidePairedShares, bytes) ← decodeUInt 4 bytes
  let (currentInsideClosingPrice, bytes) ← decodeUInt 8 bytes
  let (currentInsideImbalanceQuantity, bytes) ← decodeUInt 4 bytes
  let (currentInsideImbalanceSide, bytes) ← CurrentInsideImbalanceSide.decode bytes
  let (fullClosingPrice, bytes) ← decodeUInt 8 bytes
  let (ocioOnlyClosingPrice, bytes) ← decodeUInt 8 bytes
  let (mocSharesUnmatched, bytes) ← MocSharesUnmatched.decode bytes
  pure ({ time, symbol, currentInsidePairedShares, currentInsideClosingPrice, currentInsideImbalanceQuantity, currentInsideImbalanceSide, fullClosingPrice, ocioOnlyClosingPrice, mocSharesUnmatched }, bytes)

@[simp] theorem encode_length (message : ImbalanceMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CurrentInsideImbalanceSide.encode_length, MocSharesUnmatched.encode_length]

theorem encode_length_pos (message : ImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CurrentInsideImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MocSharesUnmatched.decode_encode, some_bind]
  rfl

end ImbalanceMessage

/-- System Recovery Event Message: 17 bytes -/
structure SystemRecoveryEventMessage where
  deprecated : BitVec 32
  recoveryType : BitVec 8
  nextSequenceNumber : BitVec 32
  recoveryStartTime : BitVec 64
  deriving DecidableEq, Repr

namespace SystemRecoveryEventMessage

def encode (message : SystemRecoveryEventMessage) : List UInt8 :=
  encodeUInt 4 message.deprecated
    ++ (encodeUInt 1 message.recoveryType
    ++ (encodeUInt 4 message.nextSequenceNumber
    ++ (encodeUInt 8 message.recoveryStartTime)))

def decode (bytes : List UInt8) : Option (SystemRecoveryEventMessage × List UInt8) := do
  let (deprecated, bytes) ← decodeUInt 4 bytes
  let (recoveryType, bytes) ← decodeUInt 1 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (recoveryStartTime, bytes) ← decodeUInt 8 bytes
  pure ({ deprecated, recoveryType, nextSequenceNumber, recoveryStartTime }, bytes)

@[simp] theorem encode_length (message : SystemRecoveryEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SystemRecoveryEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemRecoveryEventMessage) (rest : List UInt8) :
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

end SystemRecoveryEventMessage

/-- Login Request Message: 32 bytes -/
structure LoginRequestMessage where
  userId : Alpha 16
  password : Alpha 16
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.userId
    ++ (Alpha.encode message.password)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, password }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Login Response Message: 17 bytes -/
structure LoginResponseMessage where
  userId : Alpha 16
  loginStatus : BitVec 8
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  Alpha.encode message.userId
    ++ (encodeUInt 1 message.loginStatus)

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 16 bytes
  let (loginStatus, bytes) ← decodeUInt 1 bytes
  pure ({ userId, loginStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LoginResponseMessage

/-- Retransmission Request Message: 9 bytes -/
structure RetransmissionRequestMessage where
  startSequence : BitVec 32
  numberOfMessages : BitVec 32
  retranViaTcp : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUInt 4 message.startSequence
    ++ (encodeUInt 4 message.numberOfMessages
    ++ (encodeUInt 1 message.retranViaTcp))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (startSequence, bytes) ← decodeUInt 4 bytes
  let (numberOfMessages, bytes) ← decodeUInt 4 bytes
  let (retranViaTcp, bytes) ← decodeUInt 1 bytes
  pure ({ startSequence, numberOfMessages, retranViaTcp }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Retransmission Response Message: 9 bytes -/
structure RetransmissionResponseMessage where
  startSequence : BitVec 32
  numberOfMessages : BitVec 32
  retransmissionStatus : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmissionResponseMessage

def encode (message : RetransmissionResponseMessage) : List UInt8 :=
  encodeUInt 4 message.startSequence
    ++ (encodeUInt 4 message.numberOfMessages
    ++ (encodeUInt 1 message.retransmissionStatus))

def decode (bytes : List UInt8) : Option (RetransmissionResponseMessage × List UInt8) := do
  let (startSequence, bytes) ← decodeUInt 4 bytes
  let (numberOfMessages, bytes) ← decodeUInt 4 bytes
  let (retransmissionStatus, bytes) ← decodeUInt 1 bytes
  pure ({ startSequence, numberOfMessages, retransmissionStatus }, bytes)

@[simp] theorem encode_length (message : RetransmissionResponseMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RetransmissionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmissionResponseMessage

/-- Spin Request Message: 4 bytes -/
structure SpinRequestMessage where
  clientIdentifier : BitVec 32
  deriving DecidableEq, Repr

namespace SpinRequestMessage

def encode (message : SpinRequestMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier

def decode (bytes : List UInt8) : Option (SpinRequestMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier }, bytes)

@[simp] theorem encode_length (message : SpinRequestMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SpinRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpinRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SpinRequestMessage

/-- Spin Response Message: 5 bytes -/
structure SpinResponseMessage where
  clientIdentifier : BitVec 32
  spinStatus : BitVec 8
  deriving DecidableEq, Repr

namespace SpinResponseMessage

def encode (message : SpinResponseMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier
    ++ (encodeUInt 1 message.spinStatus)

def decode (bytes : List UInt8) : Option (SpinResponseMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  let (spinStatus, bytes) ← decodeUInt 1 bytes
  pure ({ clientIdentifier, spinStatus }, bytes)

@[simp] theorem encode_length (message : SpinResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SpinResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpinResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SpinResponseMessage

/-- Enhanced Spin Request Message: 4 bytes -/
structure EnhancedSpinRequestMessage where
  clientIdentifier : BitVec 32
  deriving DecidableEq, Repr

namespace EnhancedSpinRequestMessage

def encode (message : EnhancedSpinRequestMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier

def decode (bytes : List UInt8) : Option (EnhancedSpinRequestMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier }, bytes)

@[simp] theorem encode_length (message : EnhancedSpinRequestMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : EnhancedSpinRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnhancedSpinRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EnhancedSpinRequestMessage

/-- Enhanced Spin Response Message: 9 bytes -/
structure EnhancedSpinResponseMessage where
  clientIdentifier : BitVec 32
  enhancedSpinStatus : BitVec 8
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EnhancedSpinResponseMessage

def encode (message : EnhancedSpinResponseMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier
    ++ (encodeUInt 1 message.enhancedSpinStatus
    ++ (encodeUInt 4 message.lastSeqNum))

def decode (bytes : List UInt8) : Option (EnhancedSpinResponseMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  let (enhancedSpinStatus, bytes) ← decodeUInt 1 bytes
  let (lastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier, enhancedSpinStatus, lastSeqNum }, bytes)

@[simp] theorem encode_length (message : EnhancedSpinResponseMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EnhancedSpinResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnhancedSpinResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EnhancedSpinResponseMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  clientIdentifier : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HeartbeatMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | startOfSpinMessage (message : StartOfSpinMessage) -- 11
  | endOfSpinMessage (message : EndOfSpinMessage) -- 12
  | tradingSessionMessage (message : TradingSessionMessage) -- 20
  | securityMessage (message : SecurityMessage) -- 9
  | orderAddMessage (message : OrderAddMessage) -- 21
  | orderUpdateMessage (message : OrderUpdateMessage) -- 22
  | orderDeleteMessage (message : OrderDeleteMessage) -- 23
  | orderExecutionMessage (message : OrderExecutionMessage) -- 24
  | orderExecutionWithPriceMessage (message : OrderExecutionWithPriceMessage) -- 25
  | tradeMessage (message : TradeMessage) -- 26
  | topOfBookMessage (message : TopOfBookMessage) -- 27
  | imbalanceMessage (message : ImbalanceMessage) -- 28
  | systemRecoveryEventMessage (message : SystemRecoveryEventMessage) -- 74
  | loginRequestMessage (message : LoginRequestMessage) -- 108
  | loginResponseMessage (message : LoginResponseMessage) -- 97
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 114
  | retransmissionResponseMessage (message : RetransmissionResponseMessage) -- 98
  | spinRequestMessage (message : SpinRequestMessage) -- 115
  | spinResponseMessage (message : SpinResponseMessage) -- 99
  | enhancedSpinRequestMessage (message : EnhancedSpinRequestMessage) -- 116
  | enhancedSpinResponseMessage (message : EnhancedSpinResponseMessage) -- 100
  | heartbeatMessage (message : HeartbeatMessage) -- 104
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .startOfSpinMessage _ => 11
  | .endOfSpinMessage _ => 12
  | .tradingSessionMessage _ => 20
  | .securityMessage _ => 9
  | .orderAddMessage _ => 21
  | .orderUpdateMessage _ => 22
  | .orderDeleteMessage _ => 23
  | .orderExecutionMessage _ => 24
  | .orderExecutionWithPriceMessage _ => 25
  | .tradeMessage _ => 26
  | .topOfBookMessage _ => 27
  | .imbalanceMessage _ => 28
  | .systemRecoveryEventMessage _ => 74
  | .loginRequestMessage _ => 108
  | .loginResponseMessage _ => 97
  | .retransmissionRequestMessage _ => 114
  | .retransmissionResponseMessage _ => 98
  | .spinRequestMessage _ => 115
  | .spinResponseMessage _ => 99
  | .enhancedSpinRequestMessage _ => 116
  | .enhancedSpinResponseMessage _ => 100
  | .heartbeatMessage _ => 104

def encode : Payload → List UInt8
  | .startOfSpinMessage message => StartOfSpinMessage.encode message
  | .endOfSpinMessage message => EndOfSpinMessage.encode message
  | .tradingSessionMessage message => TradingSessionMessage.encode message
  | .securityMessage message => SecurityMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderUpdateMessage message => OrderUpdateMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderExecutionMessage message => OrderExecutionMessage.encode message
  | .orderExecutionWithPriceMessage message => OrderExecutionWithPriceMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .imbalanceMessage message => ImbalanceMessage.encode message
  | .systemRecoveryEventMessage message => SystemRecoveryEventMessage.encode message
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .retransmissionResponseMessage message => RetransmissionResponseMessage.encode message
  | .spinRequestMessage message => SpinRequestMessage.encode message
  | .spinResponseMessage message => SpinResponseMessage.encode message
  | .enhancedSpinRequestMessage message => EnhancedSpinRequestMessage.encode message
  | .enhancedSpinResponseMessage message => EnhancedSpinResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 52 := by
  cases message with
  | startOfSpinMessage inner =>
    simp only [encode, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [encode, EndOfSpinMessage.encode_length]
    omega
  | tradingSessionMessage inner =>
    simp only [encode, TradingSessionMessage.encode_length]
    omega
  | securityMessage inner =>
    simp only [encode, SecurityMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [encode, OrderAddMessage.encode_length]
    omega
  | orderUpdateMessage inner =>
    simp only [encode, OrderUpdateMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [encode, OrderExecutionMessage.encode_length]
    omega
  | orderExecutionWithPriceMessage inner =>
    simp only [encode, OrderExecutionWithPriceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [encode, ImbalanceMessage.encode_length]
    omega
  | systemRecoveryEventMessage inner =>
    simp only [encode, SystemRecoveryEventMessage.encode_length]
    omega
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [encode, RetransmissionResponseMessage.encode_length]
    omega
  | spinRequestMessage inner =>
    simp only [encode, SpinRequestMessage.encode_length]
    omega
  | spinResponseMessage inner =>
    simp only [encode, SpinResponseMessage.encode_length]
    omega
  | enhancedSpinRequestMessage inner =>
    simp only [encode, EnhancedSpinRequestMessage.encode_length]
    omega
  | enhancedSpinResponseMessage inner =>
    simp only [encode, EnhancedSpinResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 11 then (StartOfSpinMessage.decode bytes).map fun (message, rest) => (.startOfSpinMessage message, rest)
  else if tag = 12 then (EndOfSpinMessage.decode bytes).map fun (message, rest) => (.endOfSpinMessage message, rest)
  else if tag = 20 then (TradingSessionMessage.decode bytes).map fun (message, rest) => (.tradingSessionMessage message, rest)
  else if tag = 9 then (SecurityMessage.decode bytes).map fun (message, rest) => (.securityMessage message, rest)
  else if tag = 21 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 22 then (OrderUpdateMessage.decode bytes).map fun (message, rest) => (.orderUpdateMessage message, rest)
  else if tag = 23 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 24 then (OrderExecutionMessage.decode bytes).map fun (message, rest) => (.orderExecutionMessage message, rest)
  else if tag = 25 then (OrderExecutionWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutionWithPriceMessage message, rest)
  else if tag = 26 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 27 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 28 then (ImbalanceMessage.decode bytes).map fun (message, rest) => (.imbalanceMessage message, rest)
  else if tag = 74 then (SystemRecoveryEventMessage.decode bytes).map fun (message, rest) => (.systemRecoveryEventMessage message, rest)
  else if tag = 108 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 97 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 114 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 98 then (RetransmissionResponseMessage.decode bytes).map fun (message, rest) => (.retransmissionResponseMessage message, rest)
  else if tag = 115 then (SpinRequestMessage.decode bytes).map fun (message, rest) => (.spinRequestMessage message, rest)
  else if tag = 99 then (SpinResponseMessage.decode bytes).map fun (message, rest) => (.spinResponseMessage message, rest)
  else if tag = 116 then (EnhancedSpinRequestMessage.decode bytes).map fun (message, rest) => (.enhancedSpinRequestMessage message, rest)
  else if tag = 100 then (EnhancedSpinResponseMessage.decode bytes).map fun (message, rest) => (.enhancedSpinResponseMessage message, rest)
  else if tag = 104 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
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
  | tradingSessionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSessionMessage.encode_length]
    omega
  | securityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAddMessage.encode_length]
    omega
  | orderUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderUpdateMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutionMessage.encode_length]
    omega
  | orderExecutionWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutionWithPriceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopOfBookMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImbalanceMessage.encode_length]
    omega
  | systemRecoveryEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemRecoveryEventMessage.encode_length]
    omega
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetransmissionResponseMessage.encode_length]
    omega
  | spinRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpinRequestMessage.encode_length]
    omega
  | spinResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpinResponseMessage.encode_length]
    omega
  | enhancedSpinRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EnhancedSpinRequestMessage.encode_length]
    omega
  | enhancedSpinResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EnhancedSpinResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
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
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.OtcmarketsLinknqbRetransmissionLinkV118
