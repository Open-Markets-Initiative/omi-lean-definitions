import Wire

/-!
# Osaka Digital Exchange Proprietary Trading System v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OdxOdxequitiesPtsOuchV20Server

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

/-- System Event: one byte code -/
def SystemEvent.codes : List UInt8 :=
  [0x53, 0x45]

inductive SystemEvent where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemEvent

def toByte : SystemEvent → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemEvent :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : SystemEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemEvent) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemEvent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemEvent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemEvent

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | shortSell -- Short Sell
  | shortSellExempt -- Short Sell Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .shortSell => 0x54
  | .shortSellExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .shortSell
  else .shortSellExempt

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | shortSell => decide
  | shortSellExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x50]

inductive Display where
  | postonly -- Postonly
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .postonly => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Display :=
  .postonly

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | postonly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x41, 0x50]

inductive Capacity where
  | agency -- Agency
  | principal -- Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x41 then .agency
  else .principal

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

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

/-- Order Classification: one byte code -/
def OrderClassification.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36]

inductive OrderClassification where
  | nonHft -- Non Hft
  | hftMarketMakingStrategy -- Hft Market Making Strategy
  | hftArbitrageStrategy -- Hft Arbitrage Strategy
  | hftDirectionalStrategy -- Hft Directional Strategy
  | hftOtherStrategy -- Hft Other Strategy
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderClassification

def toByte : OrderClassification → UInt8
  | .nonHft => 0x31
  | .hftMarketMakingStrategy => 0x33
  | .hftArbitrageStrategy => 0x34
  | .hftDirectionalStrategy => 0x35
  | .hftOtherStrategy => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderClassification :=
  if byte = 0x31 then .nonHft
  else if byte = 0x33 then .hftMarketMakingStrategy
  else if byte = 0x34 then .hftArbitrageStrategy
  else if byte = 0x35 then .hftDirectionalStrategy
  else .hftOtherStrategy

def ofByte (byte : UInt8) : OrderClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderClassification) : ofByte value.toByte = value := by
  cases value with
  | nonHft => decide
  | hftMarketMakingStrategy => decide
  | hftArbitrageStrategy => decide
  | hftDirectionalStrategy => decide
  | hftOtherStrategy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderClassification) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderClassification

/-- Cash Margin Type: one byte code -/
def CashMarginType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive CashMarginType where
  | cash -- Cash
  | marginOpenNegotiable -- Margin Open Negotiable
  | marginCloseNegotiable -- Margin Close Negotiable
  | marginOpenStandardized -- Margin Open Standardized
  | marginCloseStandardized -- Margin Close Standardized
  | unlisted (byte : { byte : UInt8 // byte ∉ CashMarginType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CashMarginType

def toByte : CashMarginType → UInt8
  | .cash => 0x31
  | .marginOpenNegotiable => 0x32
  | .marginCloseNegotiable => 0x33
  | .marginOpenStandardized => 0x34
  | .marginCloseStandardized => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CashMarginType :=
  if byte = 0x31 then .cash
  else if byte = 0x32 then .marginOpenNegotiable
  else if byte = 0x33 then .marginCloseNegotiable
  else if byte = 0x34 then .marginOpenStandardized
  else .marginCloseStandardized

def ofByte (byte : UInt8) : CashMarginType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CashMarginType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | marginOpenNegotiable => decide
  | marginCloseNegotiable => decide
  | marginOpenStandardized => decide
  | marginCloseStandardized => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CashMarginType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CashMarginType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CashMarginType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CashMarginType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CashMarginType

/-- Order Canceled Reason: one byte code -/
def OrderCanceledReason.codes : List UInt8 :=
  [0x55, 0x4C, 0x53, 0x49, 0x4D, 0x58, 0x5A, 0x4E, 0x59, 0x44, 0x56, 0x69, 0x52, 0x46, 0x47, 0x4F]

inductive OrderCanceledReason where
  | userRequestedCancel -- User Requested Cancel
  | userLoggedOff -- User Logged Off
  | canceledBySupervisoryTerminal -- Canceled By Supervisory Terminal
  | immediateOrderRemainingQuantityCanceled -- Immediate Order Remaining Quantity Canceled
  | orderExpiredDuringMatch -- Order Expired During Match
  | invalidPrice -- Invalid Price
  | invalidQuantity -- Invalid Quantity
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | invalidOrderType -- Invalid Order Type
  | invalidDisplayType -- Invalid Display Type
  | exceededOrderValueLimit -- Exceeded Order Value Limit
  | shortSellOrderRestriction -- Short Sell Order Restriction
  | orderNotAllowedAtThisTime -- Order Not Allowed At This Time
  | flowControlThrottled -- Flow Control Throttled
  | marginOrderCanceledDueToMarginRestriction -- Margin Order Canceled Due To Margin Restriction
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCanceledReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCanceledReason

def toByte : OrderCanceledReason → UInt8
  | .userRequestedCancel => 0x55
  | .userLoggedOff => 0x4C
  | .canceledBySupervisoryTerminal => 0x53
  | .immediateOrderRemainingQuantityCanceled => 0x49
  | .orderExpiredDuringMatch => 0x4D
  | .invalidPrice => 0x58
  | .invalidQuantity => 0x5A
  | .invalidMinimumQuantity => 0x4E
  | .invalidOrderType => 0x59
  | .invalidDisplayType => 0x44
  | .exceededOrderValueLimit => 0x56
  | .shortSellOrderRestriction => 0x69
  | .orderNotAllowedAtThisTime => 0x52
  | .flowControlThrottled => 0x46
  | .marginOrderCanceledDueToMarginRestriction => 0x47
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCanceledReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x4C then .userLoggedOff
  else if byte = 0x53 then .canceledBySupervisoryTerminal
  else if byte = 0x49 then .immediateOrderRemainingQuantityCanceled
  else if byte = 0x4D then .orderExpiredDuringMatch
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x5A then .invalidQuantity
  else if byte = 0x4E then .invalidMinimumQuantity
  else if byte = 0x59 then .invalidOrderType
  else if byte = 0x44 then .invalidDisplayType
  else if byte = 0x56 then .exceededOrderValueLimit
  else if byte = 0x69 then .shortSellOrderRestriction
  else if byte = 0x52 then .orderNotAllowedAtThisTime
  else if byte = 0x46 then .flowControlThrottled
  else if byte = 0x47 then .marginOrderCanceledDueToMarginRestriction
  else .other

def ofByte (byte : UInt8) : OrderCanceledReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCanceledReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | userLoggedOff => decide
  | canceledBySupervisoryTerminal => decide
  | immediateOrderRemainingQuantityCanceled => decide
  | orderExpiredDuringMatch => decide
  | invalidPrice => decide
  | invalidQuantity => decide
  | invalidMinimumQuantity => decide
  | invalidOrderType => decide
  | invalidDisplayType => decide
  | exceededOrderValueLimit => decide
  | shortSellOrderRestriction => decide
  | orderNotAllowedAtThisTime => decide
  | flowControlThrottled => decide
  | marginOrderCanceledDueToMarginRestriction => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCanceledReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCanceledReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCanceledReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCanceledReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCanceledReason

/-- Liquidity Indicator: one byte code -/
def LiquidityIndicator.codes : List UInt8 :=
  [0x41, 0x52]

inductive LiquidityIndicator where
  | added -- Added
  | removed -- Removed
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityIndicator

def toByte : LiquidityIndicator → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityIndicator :=
  if byte = 0x41 then .added
  else .removed

def ofByte (byte : UInt8) : LiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityIndicator

/-- Order Rejected Reason: one byte code -/
def OrderRejectedReason.codes : List UInt8 :=
  [0x48, 0x53, 0x58, 0x5A, 0x4E, 0x59, 0x44, 0x56, 0x69, 0x52, 0x46, 0x47, 0x4C, 0x63, 0x4F]

inductive OrderRejectedReason where
  | tradingHalt -- Trading Halt
  | invalidOrderbookIdentifier -- Invalid Orderbook Identifier
  | invalidPrice -- Invalid Price
  | invalidQuantity -- Invalid Quantity
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | invalidOrderType -- Invalid Order Type
  | invalidDisplayType -- Invalid Display Type
  | exceededOrderValueLimit -- Exceeded Order Value Limit
  | shortSellOrderRestriction -- Short Sell Order Restriction
  | orderNotAllowedAtThisTime -- Order Not Allowed At This Time
  | flowControlThrottled -- Flow Control Throttled
  | invalidMarginSpecification -- Invalid Margin Specification
  | mpidNotAllowedForThisPort -- Mpid Not Allowed For This Port
  | noPermissionToEnterOrderOnGivenBoard -- No Permission To Enter Order On Given Board
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderRejectedReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderRejectedReason

def toByte : OrderRejectedReason → UInt8
  | .tradingHalt => 0x48
  | .invalidOrderbookIdentifier => 0x53
  | .invalidPrice => 0x58
  | .invalidQuantity => 0x5A
  | .invalidMinimumQuantity => 0x4E
  | .invalidOrderType => 0x59
  | .invalidDisplayType => 0x44
  | .exceededOrderValueLimit => 0x56
  | .shortSellOrderRestriction => 0x69
  | .orderNotAllowedAtThisTime => 0x52
  | .flowControlThrottled => 0x46
  | .invalidMarginSpecification => 0x47
  | .mpidNotAllowedForThisPort => 0x4C
  | .noPermissionToEnterOrderOnGivenBoard => 0x63
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderRejectedReason :=
  if byte = 0x48 then .tradingHalt
  else if byte = 0x53 then .invalidOrderbookIdentifier
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x5A then .invalidQuantity
  else if byte = 0x4E then .invalidMinimumQuantity
  else if byte = 0x59 then .invalidOrderType
  else if byte = 0x44 then .invalidDisplayType
  else if byte = 0x56 then .exceededOrderValueLimit
  else if byte = 0x69 then .shortSellOrderRestriction
  else if byte = 0x52 then .orderNotAllowedAtThisTime
  else if byte = 0x46 then .flowControlThrottled
  else if byte = 0x47 then .invalidMarginSpecification
  else if byte = 0x4C then .mpidNotAllowedForThisPort
  else if byte = 0x63 then .noPermissionToEnterOrderOnGivenBoard
  else .other

def ofByte (byte : UInt8) : OrderRejectedReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderRejectedReason) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | invalidOrderbookIdentifier => decide
  | invalidPrice => decide
  | invalidQuantity => decide
  | invalidMinimumQuantity => decide
  | invalidOrderType => decide
  | invalidDisplayType => decide
  | exceededOrderValueLimit => decide
  | shortSellOrderRestriction => decide
  | orderNotAllowedAtThisTime => decide
  | flowControlThrottled => decide
  | invalidMarginSpecification => decide
  | mpidNotAllowedForThisPort => decide
  | noPermissionToEnterOrderOnGivenBoard => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderRejectedReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderRejectedReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderRejectedReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderRejectedReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderRejectedReason

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65469
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65469 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65469 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  systemEvent : SystemEvent
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (SystemEvent.encode message.systemEvent)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (systemEvent, bytes) ← SystemEvent.decode bytes
  pure ({ timestamp, systemEvent }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SystemEvent.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SystemEvent.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Accepted Message: 64 bytes -/
structure OrderAcceptedMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  clientReference : Alpha 10
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderbookId : Alpha 4
  group : Alpha 4
  price : BitVec 32
  timeInForce : BitVec 32
  firmId : BitVec 32
  display : Display
  capacity : Capacity
  orderNumber : BitVec 64
  minimumQuantity : BitVec 32
  orderState : OrderState
  orderClassification : OrderClassification
  cashMarginType : CashMarginType
  deriving DecidableEq, Repr

namespace OrderAcceptedMessage

def encode (message : OrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (Alpha.encode message.clientReference
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.orderbookId
    ++ (Alpha.encode message.group
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (encodeUInt 4 message.firmId
    ++ (Display.encode message.display
    ++ (Capacity.encode message.capacity
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (OrderState.encode message.orderState
    ++ (OrderClassification.encode message.orderClassification
    ++ (CashMarginType.encode message.cashMarginType))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (clientReference, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderbookId, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (firmId, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (orderClassification, bytes) ← OrderClassification.decode bytes
  let (cashMarginType, bytes) ← CashMarginType.decode bytes
  pure ({ timestamp, orderToken, clientReference, buySellIndicator, quantity, orderbookId, group, price, timeInForce, firmId, display, capacity, orderNumber, minimumQuantity, orderState, orderClassification, cashMarginType }, bytes)

@[simp] theorem encode_length (message : OrderAcceptedMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BuySellIndicator.encode_length, Display.encode_length, Capacity.encode_length, OrderState.encode_length, OrderClassification.encode_length, CashMarginType.encode_length]

theorem encode_length_pos (message : OrderAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderClassification.decode_encode, some_bind]
  dsimp only
  rw [CashMarginType.decode_encode, some_bind]
  rfl

end OrderAcceptedMessage

/-- Order Replaced Message: 51 bytes -/
structure OrderReplacedMessage where
  timestamp : BitVec 64
  replacementOrderToken : BitVec 32
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderbookId : Alpha 4
  group : Alpha 4
  price : BitVec 32
  timeInForce : BitVec 32
  display : Display
  orderNumber : BitVec 64
  minimumQuantity : BitVec 32
  orderState : OrderState
  previousOrderToken : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.replacementOrderToken
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.orderbookId
    ++ (Alpha.encode message.group
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (OrderState.encode message.orderState
    ++ (encodeUInt 4 message.previousOrderToken))))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (replacementOrderToken, bytes) ← decodeUInt 4 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderbookId, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (previousOrderToken, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, replacementOrderToken, buySellIndicator, quantity, orderbookId, group, price, timeInForce, display, orderNumber, minimumQuantity, orderState, previousOrderToken }, bytes)

@[simp] theorem encode_length (message : OrderReplacedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length, Display.encode_length, OrderState.encode_length]

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplacedMessage

/-- Order Canceled Message: 17 bytes -/
structure OrderCanceledMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  decrementQuantity : BitVec 32
  orderCanceledReason : OrderCanceledReason
  deriving DecidableEq, Repr

namespace OrderCanceledMessage

def encode (message : OrderCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 4 message.decrementQuantity
    ++ (OrderCanceledReason.encode message.orderCanceledReason)))

def decode (bytes : List UInt8) : Option (OrderCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (decrementQuantity, bytes) ← decodeUInt 4 bytes
  let (orderCanceledReason, bytes) ← OrderCanceledReason.decode bytes
  pure ({ timestamp, orderToken, decrementQuantity, orderCanceledReason }, bytes)

@[simp] theorem encode_length (message : OrderCanceledMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderCanceledReason.encode_length]

theorem encode_length_pos (message : OrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderCanceledReason.decode_encode, some_bind]
  rfl

end OrderCanceledMessage

/-- Order Aiq Canceled Message: 26 bytes -/
structure OrderAiqCanceledMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  decrementQuantity : BitVec 32
  orderCanceledReason : OrderCanceledReason
  quantityPreventedFromTrading : BitVec 32
  executionPrice : BitVec 32
  liquidityIndicator : LiquidityIndicator
  deriving DecidableEq, Repr

namespace OrderAiqCanceledMessage

def encode (message : OrderAiqCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 4 message.decrementQuantity
    ++ (OrderCanceledReason.encode message.orderCanceledReason
    ++ (encodeUInt 4 message.quantityPreventedFromTrading
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityIndicator.encode message.liquidityIndicator))))))

def decode (bytes : List UInt8) : Option (OrderAiqCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (decrementQuantity, bytes) ← decodeUInt 4 bytes
  let (orderCanceledReason, bytes) ← OrderCanceledReason.decode bytes
  let (quantityPreventedFromTrading, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← LiquidityIndicator.decode bytes
  pure ({ timestamp, orderToken, decrementQuantity, orderCanceledReason, quantityPreventedFromTrading, executionPrice, liquidityIndicator }, bytes)

@[simp] theorem encode_length (message : OrderAiqCanceledMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderCanceledReason.encode_length, LiquidityIndicator.encode_length]

theorem encode_length_pos (message : OrderAiqCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAiqCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCanceledReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LiquidityIndicator.decode_encode, some_bind]
  rfl

end OrderAiqCanceledMessage

/-- Order Executed Message: 29 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  executedQuantity : BitVec 32
  executionPrice : BitVec 32
  liquidityIndicator : LiquidityIndicator
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityIndicator.encode message.liquidityIndicator
    ++ (encodeUInt 8 message.matchNumber)))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← LiquidityIndicator.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderToken, executedQuantity, executionPrice, liquidityIndicator, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LiquidityIndicator.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, LiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Rejected Message: 13 bytes -/
structure OrderRejectedMessage where
  timestamp : BitVec 64
  orderToken : BitVec 32
  orderRejectedReason : OrderRejectedReason
  deriving DecidableEq, Repr

namespace OrderRejectedMessage

def encode (message : OrderRejectedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderToken
    ++ (OrderRejectedReason.encode message.orderRejectedReason))

def decode (bytes : List UInt8) : Option (OrderRejectedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (orderRejectedReason, bytes) ← OrderRejectedReason.decode bytes
  pure ({ timestamp, orderToken, orderRejectedReason }, bytes)

@[simp] theorem encode_length (message : OrderRejectedMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderRejectedReason.encode_length]

theorem encode_length_pos (message : OrderRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderRejectedReason.decode_encode, some_bind]
  rfl

end OrderRejectedMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderAcceptedMessage (message : OrderAcceptedMessage) -- "A" 0x41
  | orderReplacedMessage (message : OrderReplacedMessage) -- "U" 0x55
  | orderCanceledMessage (message : OrderCanceledMessage) -- "C" 0x43
  | orderAiqCanceledMessage (message : OrderAiqCanceledMessage) -- "D" 0x44
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderRejectedMessage (message : OrderRejectedMessage) -- "J" 0x4A
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .orderAcceptedMessage _ => 65
  | .orderReplacedMessage _ => 85
  | .orderCanceledMessage _ => 67
  | .orderAiqCanceledMessage _ => 68
  | .orderExecutedMessage _ => 69
  | .orderRejectedMessage _ => 74

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderAcceptedMessage message => OrderAcceptedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .orderCanceledMessage message => OrderCanceledMessage.encode message
  | .orderAiqCanceledMessage message => OrderAiqCanceledMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderRejectedMessage message => OrderRejectedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 64 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderAcceptedMessage inner =>
    simp only [encode, OrderAcceptedMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [encode, OrderReplacedMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [encode, OrderCanceledMessage.encode_length]
    omega
  | orderAiqCanceledMessage inner =>
    simp only [encode, OrderAiqCanceledMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderRejectedMessage inner =>
    simp only [encode, OrderRejectedMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (OrderAcceptedMessage.decode bytes).map fun (message, rest) => (.orderAcceptedMessage message, rest)
  else if tag = 85 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 67 then (OrderCanceledMessage.decode bytes).map fun (message, rest) => (.orderCanceledMessage message, rest)
  else if tag = 68 then (OrderAiqCanceledMessage.decode bytes).map fun (message, rest) => (.orderAiqCanceledMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 74 then (OrderRejectedMessage.decode bytes).map fun (message, rest) => (.orderRejectedMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 65 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderAcceptedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderAcceptedMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplacedMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCanceledMessage.encode_length]
    omega
  | orderAiqCanceledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderAiqCanceledMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderRejectedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderRejectedMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65469 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
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

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacket := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
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
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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

end Omi.OdxOdxequitiesPtsOuchV20Server
