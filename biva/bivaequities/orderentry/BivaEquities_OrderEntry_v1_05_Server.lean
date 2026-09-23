import Omi.Wire

/-!
# Bolsa Institucional de Valores Order Entry v1.05

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BivaBivaequitiesOrderentryOuchV105Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x43, 0x48, 0x4F, 0x59, 0x4D, 0x53]

inductive AccountType where
  | client -- Client
  | house -- House
  | other -- Other
  | strategy -- Strategy
  | marketMaker -- Market Maker
  | stabilisation -- Stabilisation
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .client => 0x43
  | .house => 0x48
  | .other => 0x4F
  | .strategy => 0x59
  | .marketMaker => 0x4D
  | .stabilisation => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x43 then .client
  else if byte = 0x48 then .house
  else if byte = 0x4F then .other
  else if byte = 0x59 then .strategy
  else if byte = 0x4D then .marketMaker
  else .stabilisation

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | client => decide
  | house => decide
  | other => decide
  | strategy => decide
  | marketMaker => decide
  | stabilisation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53, 0x54]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | shortSell -- Short Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .shortSell => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .shortSell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | shortSell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Order State: one byte code -/
def OrderState.codes : List UInt8 :=
  [0x4C, 0x44]

inductive OrderState where
  | live -- Live
  | dead -- Dead
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderState

def toByte : OrderState → UInt8
  | .live => 0x4C
  | .dead => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderState :=
  if byte = 0x4C then .live
  else .dead

def ofByte (byte : UInt8) : OrderState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderState) : ofByte value.toByte = value := by
  cases value with
  | live => decide
  | dead => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderState

/-- Canceled Reason: one byte code -/
def CanceledReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x4C, 0x5A, 0x52, 0x58, 0x4E, 0x59, 0x46, 0x57]

inductive CanceledReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrderExpired -- Immediate Order Expired
  | timeoutSessionOrDayOrderExpired -- Timeout Session Or Day Order Expired
  | supervisory -- Supervisory
  | userLoggedOff -- User Logged Off
  | invalidQuantityOrQuantityExceedsMaximumLimit -- Invalid Quantity Or Quantity Exceeds Maximum Limit
  | orderNotAllowedAtThisTime -- Order Not Allowed At This Time
  | invalidPrice -- Invalid Price
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | invalidOrderType -- Invalid Order Type
  | flowControlInPlaceForUser -- Flow Control In Place For User
  | unknown -- Unknown
  | unlisted (byte : { byte : UInt8 // byte ∉ CanceledReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CanceledReason

def toByte : CanceledReason → UInt8
  | .userRequestedCancel => 0x55
  | .immediateOrderExpired => 0x49
  | .timeoutSessionOrDayOrderExpired => 0x54
  | .supervisory => 0x53
  | .userLoggedOff => 0x4C
  | .invalidQuantityOrQuantityExceedsMaximumLimit => 0x5A
  | .orderNotAllowedAtThisTime => 0x52
  | .invalidPrice => 0x58
  | .invalidMinimumQuantity => 0x4E
  | .invalidOrderType => 0x59
  | .flowControlInPlaceForUser => 0x46
  | .unknown => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CanceledReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrderExpired
  else if byte = 0x54 then .timeoutSessionOrDayOrderExpired
  else if byte = 0x53 then .supervisory
  else if byte = 0x4C then .userLoggedOff
  else if byte = 0x5A then .invalidQuantityOrQuantityExceedsMaximumLimit
  else if byte = 0x52 then .orderNotAllowedAtThisTime
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x4E then .invalidMinimumQuantity
  else if byte = 0x59 then .invalidOrderType
  else if byte = 0x46 then .flowControlInPlaceForUser
  else .unknown

def ofByte (byte : UInt8) : CanceledReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CanceledReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | immediateOrderExpired => decide
  | timeoutSessionOrDayOrderExpired => decide
  | supervisory => decide
  | userLoggedOff => decide
  | invalidQuantityOrQuantityExceedsMaximumLimit => decide
  | orderNotAllowedAtThisTime => decide
  | invalidPrice => decide
  | invalidMinimumQuantity => decide
  | invalidOrderType => decide
  | flowControlInPlaceForUser => decide
  | unknown => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CanceledReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CanceledReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CanceledReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CanceledReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CanceledReason

/-- Liquidity Flag: one byte code -/
def LiquidityFlag.codes : List UInt8 :=
  [0x41, 0x52, 0x55]

inductive LiquidityFlag where
  | addedForThePassiveFirm -- Added For The Passive Firm
  | removedForTheAggressor -- Removed For The Aggressor
  | uncrossForAuctionExecutions -- Uncross For Auction Executions
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityFlag

def toByte : LiquidityFlag → UInt8
  | .addedForThePassiveFirm => 0x41
  | .removedForTheAggressor => 0x52
  | .uncrossForAuctionExecutions => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityFlag :=
  if byte = 0x41 then .addedForThePassiveFirm
  else if byte = 0x52 then .removedForTheAggressor
  else .uncrossForAuctionExecutions

def ofByte (byte : UInt8) : LiquidityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityFlag) : ofByte value.toByte = value := by
  cases value with
  | addedForThePassiveFirm => decide
  | removedForTheAggressor => decide
  | uncrossForAuctionExecutions => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityFlag

/-- Broken Trade Reason: one byte code -/
def BrokenTradeReason.codes : List UInt8 :=
  [0x43, 0x53]

inductive BrokenTradeReason where
  | consentBothPartiesAgreedToBreakTheTrade -- Consent Both Parties Agreed To Break The Trade
  | supervisoryBrokenByBivaMarketControl -- Supervisory Broken By Biva Market Control
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokenTradeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokenTradeReason

def toByte : BrokenTradeReason → UInt8
  | .consentBothPartiesAgreedToBreakTheTrade => 0x43
  | .supervisoryBrokenByBivaMarketControl => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokenTradeReason :=
  if byte = 0x43 then .consentBothPartiesAgreedToBreakTheTrade
  else .supervisoryBrokenByBivaMarketControl

def ofByte (byte : UInt8) : BrokenTradeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokenTradeReason) : ofByte value.toByte = value := by
  cases value with
  | consentBothPartiesAgreedToBreakTheTrade => decide
  | supervisoryBrokenByBivaMarketControl => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokenTradeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokenTradeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokenTradeReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BrokenTradeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokenTradeReason

/-- Rejected Reason: one byte code -/
def RejectedReason.codes : List UInt8 :=
  [0x48, 0x5A, 0x53, 0x52, 0x58, 0x4E, 0x59, 0x46, 0x57]

inductive RejectedReason where
  | secboardInstrumentBoardOrMarketNotTradeable -- Secboard Instrument Board Or Market Not Tradeable
  | invalidQuantityOrQuantityExceedsMaximumLimit -- Invalid Quantity Or Quantity Exceeds Maximum Limit
  | invalidOrderbookIdentifier -- Invalid Orderbook Identifier
  | orderNotAllowedAtThisTime -- Order Not Allowed At This Time
  | invalidPrice -- Invalid Price
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | invalidOrderType -- Invalid Order Type
  | flowControlInPlaceForUser -- Flow Control In Place For User
  | unknown -- Unknown
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectedReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectedReason

def toByte : RejectedReason → UInt8
  | .secboardInstrumentBoardOrMarketNotTradeable => 0x48
  | .invalidQuantityOrQuantityExceedsMaximumLimit => 0x5A
  | .invalidOrderbookIdentifier => 0x53
  | .orderNotAllowedAtThisTime => 0x52
  | .invalidPrice => 0x58
  | .invalidMinimumQuantity => 0x4E
  | .invalidOrderType => 0x59
  | .flowControlInPlaceForUser => 0x46
  | .unknown => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectedReason :=
  if byte = 0x48 then .secboardInstrumentBoardOrMarketNotTradeable
  else if byte = 0x5A then .invalidQuantityOrQuantityExceedsMaximumLimit
  else if byte = 0x53 then .invalidOrderbookIdentifier
  else if byte = 0x52 then .orderNotAllowedAtThisTime
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x4E then .invalidMinimumQuantity
  else if byte = 0x59 then .invalidOrderType
  else if byte = 0x46 then .flowControlInPlaceForUser
  else .unknown

def ofByte (byte : UInt8) : RejectedReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectedReason) : ofByte value.toByte = value := by
  cases value with
  | secboardInstrumentBoardOrMarketNotTradeable => decide
  | invalidQuantityOrQuantityExceedsMaximumLimit => decide
  | invalidOrderbookIdentifier => decide
  | orderNotAllowedAtThisTime => decide
  | invalidPrice => decide
  | invalidMinimumQuantity => decide
  | invalidOrderType => decide
  | flowControlInPlaceForUser => decide
  | unknown => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectedReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectedReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectedReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectedReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectedReason

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Accepted Message: 59 bytes -/
structure AcceptedMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  accountType : AccountType
  accountId : BitVec 32
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 32
  timeInForce : BitVec 32
  clientId : BitVec 32
  orderReferenceNumber : BitVec 64
  minimumQuantity : BitVec 64
  orderState : OrderState
  deriving DecidableEq, Repr

namespace AcceptedMessage

def encode (message : AcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (AccountType.encode message.accountType
    ++ (encodeUInt 4 message.accountId
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (encodeUInt 4 message.clientId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 8 message.minimumQuantity
    ++ (OrderState.encode message.orderState))))))))))))

def decode (bytes : List UInt8) : Option (AcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (accountId, bytes) ← decodeUInt 4 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (clientId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 8 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  pure ({ timestamp, orderToken, accountType, accountId, orderVerb, quantity, orderbook, price, timeInForce, clientId, orderReferenceNumber, minimumQuantity, orderState }, bytes)

@[simp] theorem encode_length (message : AcceptedMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AccountType.encode_length, OrderVerb.encode_length, OrderState.encode_length]

theorem encode_length_pos (message : AcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
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
  rw [OrderState.decode_encode, some_bind]
  rfl

end AcceptedMessage

/-- Replaced Message: 42 bytes -/
structure ReplacedMessage where
  timestamp : BitVec 64
  replacementOrderToken : BitVec 32
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 32
  orderReferenceNumber : BitVec 64
  orderState : OrderState
  previousOrderToken : BitVec 32
  deriving DecidableEq, Repr

namespace ReplacedMessage

def encode (message : ReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.replacementOrderToken
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (OrderState.encode message.orderState
    ++ (encodeUInt 4 message.previousOrderToken))))))))

def decode (bytes : List UInt8) : Option (ReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (replacementOrderToken, bytes) ← decodeUInt 4 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (previousOrderToken, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, replacementOrderToken, orderVerb, quantity, orderbook, price, orderReferenceNumber, orderState, previousOrderToken }, bytes)

@[simp] theorem encode_length (message : ReplacedMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length, OrderState.encode_length]

theorem encode_length_pos (message : ReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplacedMessage

/-- Canceled Message: 21 bytes -/
structure CanceledMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  quantity : BitVec 64
  canceledReason : CanceledReason
  deriving DecidableEq, Repr

namespace CanceledMessage

def encode (message : CanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 8 message.quantity
    ++ (CanceledReason.encode message.canceledReason)))

def decode (bytes : List UInt8) : Option (CanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (canceledReason, bytes) ← CanceledReason.decode bytes
  pure ({ timestamp, orderToken, quantity, canceledReason }, bytes)

@[simp] theorem encode_length (message : CanceledMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CanceledReason.encode_length]

theorem encode_length_pos (message : CanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CanceledReason.decode_encode, some_bind]
  rfl

end CanceledMessage

/-- Executed Order Message: 37 bytes -/
structure ExecutedOrderMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  executedQuantity : BitVec 64
  executedPrice : BitVec 32
  liquidityFlag : LiquidityFlag
  matchNumber : BitVec 64
  counterPartyId : BitVec 32
  deriving DecidableEq, Repr

namespace ExecutedOrderMessage

def encode (message : ExecutedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 4 message.executedPrice
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 8 message.matchNumber
    ++ (encodeUInt 4 message.counterPartyId))))))

def decode (bytes : List UInt8) : Option (ExecutedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (executedPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (counterPartyId, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderToken, executedQuantity, executedPrice, liquidityFlag, matchNumber, counterPartyId }, bytes)

@[simp] theorem encode_length (message : ExecutedOrderMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LiquidityFlag.encode_length]

theorem encode_length_pos (message : ExecutedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutedOrderMessage

/-- Broken Trade Message: 21 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  matchNumber : BitVec 64
  brokenTradeReason : BrokenTradeReason
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 8 message.matchNumber
    ++ (BrokenTradeReason.encode message.brokenTradeReason)))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (brokenTradeReason, bytes) ← BrokenTradeReason.decode bytes
  pure ({ timestamp, orderToken, matchNumber, brokenTradeReason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BrokenTradeReason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BrokenTradeReason.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Rejected Order Message: 13 bytes -/
structure RejectedOrderMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  rejectedReason : RejectedReason
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

def encode (message : RejectedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (RejectedReason.encode message.rejectedReason))

def decode (bytes : List UInt8) : Option (RejectedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (rejectedReason, bytes) ← RejectedReason.decode bytes
  pure ({ timestamp, orderToken, rejectedReason }, bytes)

@[simp] theorem encode_length (message : RejectedOrderMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, RejectedReason.encode_length]

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [RejectedReason.decode_encode, some_bind]
  rfl

end RejectedOrderMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | acceptedMessage (message : AcceptedMessage) -- "A" 0x41
  | replacedMessage (message : ReplacedMessage) -- "U" 0x55
  | canceledMessage (message : CanceledMessage) -- "C" 0x43
  | executedOrderMessage (message : ExecutedOrderMessage) -- "E" 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | rejectedOrderMessage (message : RejectedOrderMessage) -- "J" 0x4A
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .acceptedMessage _ => 65
  | .replacedMessage _ => 85
  | .canceledMessage _ => 67
  | .executedOrderMessage _ => 69
  | .brokenTradeMessage _ => 66
  | .rejectedOrderMessage _ => 74

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .acceptedMessage message => AcceptedMessage.encode message
  | .replacedMessage message => ReplacedMessage.encode message
  | .canceledMessage message => CanceledMessage.encode message
  | .executedOrderMessage message => ExecutedOrderMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 59 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | acceptedMessage inner =>
    simp only [encode, AcceptedMessage.encode_length]
    omega
  | replacedMessage inner =>
    simp only [encode, ReplacedMessage.encode_length]
    omega
  | canceledMessage inner =>
    simp only [encode, CanceledMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [encode, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [encode, RejectedOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AcceptedMessage.decode bytes).map fun (message, rest) => (.acceptedMessage message, rest)
  else if tag = 85 then (ReplacedMessage.decode bytes).map fun (message, rest) => (.replacedMessage message, rest)
  else if tag = 67 then (CanceledMessage.decode bytes).map fun (message, rest) => (.canceledMessage message, rest)
  else if tag = 69 then (ExecutedOrderMessage.decode bytes).map fun (message, rest) => (.executedOrderMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun (message, rest) => (.rejectedOrderMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 60 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | acceptedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AcceptedMessage.encode_length]
    omega
  | replacedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ReplacedMessage.encode_length]
    omega
  | canceledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CanceledMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RejectedOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 60 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.BivaBivaequitiesOrderentryOuchV105Server
