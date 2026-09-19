import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Orders v4.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesOrdersOuchV42Server

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDayThisIsAlwaysTheFirstMessageEachDay -- Start Of Day— This Is Always The First Message Each Day
  | endOfDayThisIndicatesThatNasdaqIsNowClosedAndWillNotAcceptAnyNewOrdersOrReplacesInThisSession -- End Of Day— This Indicates That Nasdaq Is Now Closed And Will Not Accept Any New Orders Or Replaces In This Session
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDayThisIsAlwaysTheFirstMessageEachDay => 0x53
  | .endOfDayThisIndicatesThatNasdaqIsNowClosedAndWillNotAcceptAnyNewOrdersOrReplacesInThisSession => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDayThisIsAlwaysTheFirstMessageEachDay
  else .endOfDayThisIndicatesThatNasdaqIsNowClosedAndWillNotAcceptAnyNewOrdersOrReplacesInThisSession

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDayThisIsAlwaysTheFirstMessageEachDay => decide
  | endOfDayThisIndicatesThatNasdaqIsNowClosedAndWillNotAcceptAnyNewOrdersOrReplacesInThisSession => decide
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

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .sellShort => 0x54
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
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
  [0x41, 0x59, 0x4E, 0x50, 0x49, 0x4D, 0x57, 0x4C, 0x4F, 0x54, 0x51, 0x6D, 0x6E]

inductive Display where
  | attributablePrice -- Attributable Price
  | anonymousPrice -- Anonymous Price
  | nonDisplay -- Non Display
  | postOnly -- Post Only
  | imbalanceOnly -- Imbalance Only
  | midPoint -- Mid Point
  | midPoint_57 -- Mid Point
  | postOnlyAndAttributable -- Post Only And Attributable
  | retailOrder -- Retail Order
  | retailOrder_54 -- Retail Order
  | retailPrice -- Retail Price
  | midPoint_6d -- Mid Point
  | nonDisplayAndMidPoint -- Non Display And Mid Point
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .attributablePrice => 0x41
  | .anonymousPrice => 0x59
  | .nonDisplay => 0x4E
  | .postOnly => 0x50
  | .imbalanceOnly => 0x49
  | .midPoint => 0x4D
  | .midPoint_57 => 0x57
  | .postOnlyAndAttributable => 0x4C
  | .retailOrder => 0x4F
  | .retailOrder_54 => 0x54
  | .retailPrice => 0x51
  | .midPoint_6d => 0x6D
  | .nonDisplayAndMidPoint => 0x6E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x41 then .attributablePrice
  else if byte = 0x59 then .anonymousPrice
  else if byte = 0x4E then .nonDisplay
  else if byte = 0x50 then .postOnly
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x4D then .midPoint
  else if byte = 0x57 then .midPoint_57
  else if byte = 0x4C then .postOnlyAndAttributable
  else if byte = 0x4F then .retailOrder
  else if byte = 0x54 then .retailOrder_54
  else if byte = 0x51 then .retailPrice
  else if byte = 0x6D then .midPoint_6d
  else .nonDisplayAndMidPoint

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | attributablePrice => decide
  | anonymousPrice => decide
  | nonDisplay => decide
  | postOnly => decide
  | imbalanceOnly => decide
  | midPoint => decide
  | midPoint_57 => decide
  | postOnlyAndAttributable => decide
  | retailOrder => decide
  | retailOrder_54 => decide
  | retailPrice => decide
  | midPoint_6d => decide
  | nonDisplayAndMidPoint => decide
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
  [0x4F, 0x41, 0x50, 0x52]

inductive Capacity where
  | other -- Other
  | agency -- Agency
  | principal -- Principal
  | riskless -- Riskless
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .other => 0x4F
  | .agency => 0x41
  | .principal => 0x50
  | .riskless => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x4F then .other
  else if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .riskless

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | other => decide
  | agency => decide
  | principal => decide
  | riskless => decide
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

/-- Intermarket Sweep Eligibility: one byte code -/
def IntermarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E, 0x79]

inductive IntermarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | tradeat -- Tradeat
  | unlisted (byte : { byte : UInt8 // byte ∉ IntermarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IntermarketSweepEligibility

def toByte : IntermarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .tradeat => 0x79
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IntermarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else if byte = 0x4E then .notEligible
  else .tradeat

def ofByte (byte : UInt8) : IntermarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IntermarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | tradeat => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IntermarketSweepEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IntermarketSweepEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IntermarketSweepEligibility) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IntermarketSweepEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IntermarketSweepEligibility

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4E, 0x4F, 0x43, 0x48, 0x53, 0x52, 0x45]

inductive CrossType where
  | noCross -- No Cross
  | opening -- Opening
  | closing -- Closing
  | haltIpoCross -- Halt Ipo Cross
  | supplemental -- Supplemental
  | retail -- Retail
  | extended -- Extended
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .noCross => 0x4E
  | .opening => 0x4F
  | .closing => 0x43
  | .haltIpoCross => 0x48
  | .supplemental => 0x53
  | .retail => 0x52
  | .extended => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4E then .noCross
  else if byte = 0x4F then .opening
  else if byte = 0x43 then .closing
  else if byte = 0x48 then .haltIpoCross
  else if byte = 0x53 then .supplemental
  else if byte = 0x52 then .retail
  else .extended

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | noCross => decide
  | opening => decide
  | closing => decide
  | haltIpoCross => decide
  | supplemental => decide
  | retail => decide
  | extended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Order State: one byte code -/
def OrderState.codes : List UInt8 :=
  [0x4C, 0x44]

inductive OrderState where
  | order -- Order
  | order_44 -- Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderState

def toByte : OrderState → UInt8
  | .order => 0x4C
  | .order_44 => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderState :=
  if byte = 0x4C then .order
  else .order_44

def ofByte (byte : UInt8) : OrderState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderState) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | order_44 => decide
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

/-- Bbo Weight Indicator: one byte code -/
def BboWeightIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x53, 0x4E]

inductive BboWeightIndicator where
  | lessThanPointTwoPercent -- Less Than Point Two Percent
  | lessThanOnePercent -- Less Than One Percent
  | lessThanTwoPercent -- Less Than Two Percent
  | greaterThanTwoPercent -- Greater Than Two Percent
  | setsTheQbbo -- Sets The Qbbo
  | improvesTheNbboUponEntry -- Improves The Nbbo Upon Entry
  | unlisted (byte : { byte : UInt8 // byte ∉ BboWeightIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BboWeightIndicator

def toByte : BboWeightIndicator → UInt8
  | .lessThanPointTwoPercent => 0x30
  | .lessThanOnePercent => 0x31
  | .lessThanTwoPercent => 0x32
  | .greaterThanTwoPercent => 0x33
  | .setsTheQbbo => 0x53
  | .improvesTheNbboUponEntry => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BboWeightIndicator :=
  if byte = 0x30 then .lessThanPointTwoPercent
  else if byte = 0x31 then .lessThanOnePercent
  else if byte = 0x32 then .lessThanTwoPercent
  else if byte = 0x33 then .greaterThanTwoPercent
  else if byte = 0x53 then .setsTheQbbo
  else .improvesTheNbboUponEntry

def ofByte (byte : UInt8) : BboWeightIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BboWeightIndicator) : ofByte value.toByte = value := by
  cases value with
  | lessThanPointTwoPercent => decide
  | lessThanOnePercent => decide
  | lessThanTwoPercent => decide
  | greaterThanTwoPercent => decide
  | setsTheQbbo => decide
  | improvesTheNbboUponEntry => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BboWeightIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BboWeightIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BboWeightIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BboWeightIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BboWeightIndicator

/-- Cancel Order Reason: one byte code -/
def CancelOrderReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x5A, 0x43, 0x4B, 0x48, 0x58, 0x45, 0x46, 0x47]

inductive CancelOrderReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrCancelOrder -- Immediate Or Cancel Order
  | timeout -- Timeout
  | supervisory -- Supervisory
  | thisOrderCannotBeExecutedBecauseOfARegulatoryRestriction -- This Order Cannot Be Executed Because Of A Regulatory Restriction
  | selfMatchPrevention -- Self Match Prevention
  | systemCancel -- System Cancel
  | crossCanceled -- Cross Canceled
  | thisOrderCannotBeExecuted -- This Order Cannot Be Executed
  | halted -- Halted
  | openProtection -- Open Protection
  | closed -- Closed
  | postOnlyCancel -- Post Only Cancel
  | postOnlyCancel_47 -- Post Only Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelOrderReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelOrderReason

def toByte : CancelOrderReason → UInt8
  | .userRequestedCancel => 0x55
  | .immediateOrCancelOrder => 0x49
  | .timeout => 0x54
  | .supervisory => 0x53
  | .thisOrderCannotBeExecutedBecauseOfARegulatoryRestriction => 0x44
  | .selfMatchPrevention => 0x51
  | .systemCancel => 0x5A
  | .crossCanceled => 0x43
  | .thisOrderCannotBeExecuted => 0x4B
  | .halted => 0x48
  | .openProtection => 0x58
  | .closed => 0x45
  | .postOnlyCancel => 0x46
  | .postOnlyCancel_47 => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelOrderReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrCancelOrder
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisory
  else if byte = 0x44 then .thisOrderCannotBeExecutedBecauseOfARegulatoryRestriction
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x5A then .systemCancel
  else if byte = 0x43 then .crossCanceled
  else if byte = 0x4B then .thisOrderCannotBeExecuted
  else if byte = 0x48 then .halted
  else if byte = 0x58 then .openProtection
  else if byte = 0x45 then .closed
  else if byte = 0x46 then .postOnlyCancel
  else .postOnlyCancel_47

def ofByte (byte : UInt8) : CancelOrderReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelOrderReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | immediateOrCancelOrder => decide
  | timeout => decide
  | supervisory => decide
  | thisOrderCannotBeExecutedBecauseOfARegulatoryRestriction => decide
  | selfMatchPrevention => decide
  | systemCancel => decide
  | crossCanceled => decide
  | thisOrderCannotBeExecuted => decide
  | halted => decide
  | openProtection => decide
  | closed => decide
  | postOnlyCancel => decide
  | postOnlyCancel_47 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelOrderReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelOrderReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelOrderReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelOrderReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelOrderReason

/-- Liquidity Flag: one byte code -/
def LiquidityFlag.codes : List UInt8 :=
  [0x41, 0x52, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x4A, 0x57, 0x6D, 0x6B, 0x30, 0x37, 0x38, 0x64, 0x65, 0x66, 0x6A, 0x72, 0x74, 0x34, 0x35, 0x36, 0x67, 0x6E]

inductive LiquidityFlag where
  | added -- Added
  | removed -- Removed
  | opening -- Opening
  | openingCross -- Opening Cross
  | closing -- Closing
  | closingCross -- Closing Cross
  | haltIpo -- Halt Ipo
  | halt -- Halt
  | nondisplayed -- Nondisplayed
  | added_57 -- Added
  | removed_6d -- Removed
  | added_6b -- Added
  | supplemental -- Supplemental
  | displayed -- Displayed
  | displayed_38 -- Displayed
  | retailDesignated -- Retail Designated
  | retailDesignated_65 -- Retail Designated
  | retailDesignated_66 -- Retail Designated
  | rpiRetailPriceImproving -- Rpi Retail Price Improving
  | retailOrder -- Retail Order
  | retailOrder_74 -- Retail Order
  | added_34 -- Added
  | added_35 -- Added
  | removed_36 -- Removed
  | added_67 -- Added
  | midpoint -- Midpoint
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityFlag

def toByte : LiquidityFlag → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .opening => 0x4F
  | .openingCross => 0x4D
  | .closing => 0x43
  | .closingCross => 0x4C
  | .haltIpo => 0x48
  | .halt => 0x4B
  | .nondisplayed => 0x4A
  | .added_57 => 0x57
  | .removed_6d => 0x6D
  | .added_6b => 0x6B
  | .supplemental => 0x30
  | .displayed => 0x37
  | .displayed_38 => 0x38
  | .retailDesignated => 0x64
  | .retailDesignated_65 => 0x65
  | .retailDesignated_66 => 0x66
  | .rpiRetailPriceImproving => 0x6A
  | .retailOrder => 0x72
  | .retailOrder_74 => 0x74
  | .added_34 => 0x34
  | .added_35 => 0x35
  | .removed_36 => 0x36
  | .added_67 => 0x67
  | .midpoint => 0x6E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityFlag :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x4F then .opening
  else if byte = 0x4D then .openingCross
  else if byte = 0x43 then .closing
  else if byte = 0x4C then .closingCross
  else if byte = 0x48 then .haltIpo
  else if byte = 0x4B then .halt
  else if byte = 0x4A then .nondisplayed
  else if byte = 0x57 then .added_57
  else if byte = 0x6D then .removed_6d
  else if byte = 0x6B then .added_6b
  else if byte = 0x30 then .supplemental
  else if byte = 0x37 then .displayed
  else if byte = 0x38 then .displayed_38
  else if byte = 0x64 then .retailDesignated
  else if byte = 0x65 then .retailDesignated_65
  else if byte = 0x66 then .retailDesignated_66
  else if byte = 0x6A then .rpiRetailPriceImproving
  else if byte = 0x72 then .retailOrder
  else if byte = 0x74 then .retailOrder_74
  else if byte = 0x34 then .added_34
  else if byte = 0x35 then .added_35
  else if byte = 0x36 then .removed_36
  else if byte = 0x67 then .added_67
  else .midpoint

def ofByte (byte : UInt8) : LiquidityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityFlag) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | opening => decide
  | openingCross => decide
  | closing => decide
  | closingCross => decide
  | haltIpo => decide
  | halt => decide
  | nondisplayed => decide
  | added_57 => decide
  | removed_6d => decide
  | added_6b => decide
  | supplemental => decide
  | displayed => decide
  | displayed_38 => decide
  | retailDesignated => decide
  | retailDesignated_65 => decide
  | retailDesignated_66 => decide
  | rpiRetailPriceImproving => decide
  | retailOrder => decide
  | retailOrder_74 => decide
  | added_34 => decide
  | added_35 => decide
  | removed_36 => decide
  | added_67 => decide
  | midpoint => decide
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
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

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
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
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

/-- Accepted Message: 65 bytes -/
structure AcceptedMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  timeInForce : BitVec 32
  firm : Alpha 4
  display : Display
  orderReferenceNumber : BitVec 64
  capacity : Capacity
  intermarketSweepEligibility : IntermarketSweepEligibility
  minimumQuantity : BitVec 32
  crossType : CrossType
  orderState : OrderState
  bboWeightIndicator : BboWeightIndicator
  deriving DecidableEq, Repr

namespace AcceptedMessage

def encode (message : AcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Alpha.encode message.firm
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Capacity.encode message.capacity
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (CrossType.encode message.crossType
    ++ (OrderState.encode message.orderState
    ++ (BboWeightIndicator.encode message.bboWeightIndicator)))))))))))))))

def decode (bytes : List UInt8) : Option (AcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (bboWeightIndicator, bytes) ← BboWeightIndicator.decode bytes
  pure ({ timestamp, orderToken, buySellIndicator, shares, stock, price, timeInForce, firm, display, orderReferenceNumber, capacity, intermarketSweepEligibility, minimumQuantity, crossType, orderState, bboWeightIndicator }, bytes)

@[simp] theorem encode_length (message : AcceptedMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BuySellIndicator.encode_length, Display.encode_length, Capacity.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length, OrderState.encode_length, BboWeightIndicator.encode_length]

theorem encode_length_pos (message : AcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [BboWeightIndicator.decode_encode, some_bind]
  rfl

end AcceptedMessage

/-- Replaced Message: 79 bytes -/
structure ReplacedMessage where
  timestamp : BitVec 64
  replacementOrderTokenAlphanumeric14 : Alpha 14
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  timeInForce : BitVec 32
  firm : Alpha 4
  display : Display
  orderReferenceNumber : BitVec 64
  capacity : Capacity
  intermarketSweepEligibility : IntermarketSweepEligibility
  minimumQuantity : BitVec 32
  crossType : CrossType
  orderState : OrderState
  previousOrderToken : Alpha 14
  bboWeightIndicator : BboWeightIndicator
  deriving DecidableEq, Repr

namespace ReplacedMessage

def encode (message : ReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.replacementOrderTokenAlphanumeric14
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (Alpha.encode message.firm
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Capacity.encode message.capacity
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (CrossType.encode message.crossType
    ++ (OrderState.encode message.orderState
    ++ (Alpha.encode message.previousOrderToken
    ++ (BboWeightIndicator.encode message.bboWeightIndicator))))))))))))))))

def decode (bytes : List UInt8) : Option (ReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (replacementOrderTokenAlphanumeric14, bytes) ← Alpha.decode 14 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (previousOrderToken, bytes) ← Alpha.decode 14 bytes
  let (bboWeightIndicator, bytes) ← BboWeightIndicator.decode bytes
  pure ({ timestamp, replacementOrderTokenAlphanumeric14, buySellIndicator, shares, stock, price, timeInForce, firm, display, orderReferenceNumber, capacity, intermarketSweepEligibility, minimumQuantity, crossType, orderState, previousOrderToken, bboWeightIndicator }, bytes)

@[simp] theorem encode_length (message : ReplacedMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BuySellIndicator.encode_length, Display.encode_length, Capacity.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length, OrderState.encode_length, BboWeightIndicator.encode_length]

theorem encode_length_pos (message : ReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BboWeightIndicator.decode_encode, some_bind]
  rfl

end ReplacedMessage

/-- Canceled Message: 27 bytes -/
structure CanceledMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  decrementShares : BitVec 32
  cancelOrderReason : CancelOrderReason
  deriving DecidableEq, Repr

namespace CanceledMessage

def encode (message : CanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.decrementShares
    ++ (CancelOrderReason.encode message.cancelOrderReason)))

def decode (bytes : List UInt8) : Option (CanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (decrementShares, bytes) ← decodeUInt 4 bytes
  let (cancelOrderReason, bytes) ← CancelOrderReason.decode bytes
  pure ({ timestamp, orderToken, decrementShares, cancelOrderReason }, bytes)

@[simp] theorem encode_length (message : CanceledMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CancelOrderReason.encode_length]

theorem encode_length_pos (message : CanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelOrderReason.decode_encode, some_bind]
  rfl

end CanceledMessage

/-- Aiq Cancelled Message: 36 bytes -/
structure AiqCancelledMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  decrementShares : BitVec 32
  cancelOrderReason : CancelOrderReason
  quantityPreventedFromTrading : BitVec 32
  executionPrice : BitVec 32
  liquidityFlag : LiquidityFlag
  deriving DecidableEq, Repr

namespace AiqCancelledMessage

def encode (message : AiqCancelledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.decrementShares
    ++ (CancelOrderReason.encode message.cancelOrderReason
    ++ (encodeUInt 4 message.quantityPreventedFromTrading
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityFlag.encode message.liquidityFlag))))))

def decode (bytes : List UInt8) : Option (AiqCancelledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (decrementShares, bytes) ← decodeUInt 4 bytes
  let (cancelOrderReason, bytes) ← CancelOrderReason.decode bytes
  let (quantityPreventedFromTrading, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  pure ({ timestamp, orderToken, decrementShares, cancelOrderReason, quantityPreventedFromTrading, executionPrice, liquidityFlag }, bytes)

@[simp] theorem encode_length (message : AiqCancelledMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CancelOrderReason.encode_length, LiquidityFlag.encode_length]

theorem encode_length_pos (message : AiqCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AiqCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CancelOrderReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LiquidityFlag.decode_encode, some_bind]
  rfl

end AiqCancelledMessage

/-- Executed Message: 39 bytes -/
structure ExecutedMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  executedShares : BitVec 32
  executionPrice : BitVec 32
  liquidityFlag : LiquidityFlag
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutedMessage

def encode (message : ExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 8 message.matchNumber)))))

def decode (bytes : List UInt8) : Option (ExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderToken, executedShares, executionPrice, liquidityFlag, matchNumber }, bytes)

@[simp] theorem encode_length (message : ExecutedMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, LiquidityFlag.encode_length]

theorem encode_length_pos (message : ExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutedMessage

/-- Broken Trade Message: 31 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  matchNumber : BitVec 64
  brokenTradeReason : Alpha 1
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 8 message.matchNumber
    ++ (Alpha.encode message.brokenTradeReason)))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (brokenTradeReason, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, orderToken, matchNumber, brokenTradeReason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Executed With Reference Price Message: 44 bytes -/
structure ExecutedWithReferencePriceMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  executedShares : BitVec 32
  executionPrice : BitVec 32
  liquidityFlag : LiquidityFlag
  matchNumber : BitVec 64
  referencePrice : BitVec 32
  referencePriceType : Alpha 1
  deriving DecidableEq, Repr

namespace ExecutedWithReferencePriceMessage

def encode (message : ExecutedWithReferencePriceMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 8 message.matchNumber
    ++ (encodeUInt 4 message.referencePrice
    ++ (Alpha.encode message.referencePriceType)))))))

def decode (bytes : List UInt8) : Option (ExecutedWithReferencePriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (referencePrice, bytes) ← decodeUInt 4 bytes
  let (referencePriceType, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, orderToken, executedShares, executionPrice, liquidityFlag, matchNumber, referencePrice, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExecutedWithReferencePriceMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, LiquidityFlag.encode_length]

theorem encode_length_pos (message : ExecutedWithReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedWithReferencePriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutedWithReferencePriceMessage

/-- Trade Correction Message: 40 bytes -/
structure TradeCorrectionMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  executedShares : BitVec 32
  executionPrice : BitVec 32
  liquidityFlag : LiquidityFlag
  matchNumber : BitVec 64
  reason : Alpha 1
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 4 message.executionPrice
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 8 message.matchNumber
    ++ (Alpha.encode message.reason))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, orderToken, executedShares, executionPrice, liquidityFlag, matchNumber, reason }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, LiquidityFlag.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Rejected Order Message: 23 bytes -/
structure RejectedOrderMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  rejectedOrderReason : Alpha 1
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

def encode (message : RejectedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (Alpha.encode message.rejectedOrderReason))

def decode (bytes : List UInt8) : Option (RejectedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (rejectedOrderReason, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, orderToken, rejectedOrderReason }, bytes)

@[simp] theorem encode_length (message : RejectedOrderMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectedOrderMessage

/-- Cancel Pending Message: 22 bytes -/
structure CancelPendingMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace CancelPendingMessage

def encode (message : CancelPendingMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken)

def decode (bytes : List UInt8) : Option (CancelPendingMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ timestamp, orderToken }, bytes)

@[simp] theorem encode_length (message : CancelPendingMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelPendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelPendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelPendingMessage

/-- Cancel Reject Message: 22 bytes -/
structure CancelRejectMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace CancelRejectMessage

def encode (message : CancelRejectMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken)

def decode (bytes : List UInt8) : Option (CancelRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ timestamp, orderToken }, bytes)

@[simp] theorem encode_length (message : CancelRejectMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelRejectMessage

/-- Order Priority Update Message: 35 bytes -/
structure OrderPriorityUpdateMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  price : BitVec 32
  display : Display
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateMessage

def encode (message : OrderPriorityUpdateMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.price
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber))))

def decode (bytes : List UInt8) : Option (OrderPriorityUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderToken, price, display, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderPriorityUpdateMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Display.encode_length]

theorem encode_length_pos (message : OrderPriorityUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriorityUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderPriorityUpdateMessage

/-- Order Modified Message: 27 bytes -/
structure OrderModifiedMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  deriving DecidableEq, Repr

namespace OrderModifiedMessage

def encode (message : OrderModifiedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.shares)))

def decode (bytes : List UInt8) : Option (OrderModifiedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderToken, buySellIndicator, shares }, bytes)

@[simp] theorem encode_length (message : OrderModifiedMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : OrderModifiedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifiedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderModifiedMessage

/-- Sequenced Trade Now Message: 22 bytes -/
structure SequencedTradeNowMessage where
  timestamp : BitVec 64
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace SequencedTradeNowMessage

def encode (message : SequencedTradeNowMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.orderToken)

def decode (bytes : List UInt8) : Option (SequencedTradeNowMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ timestamp, orderToken }, bytes)

@[simp] theorem encode_length (message : SequencedTradeNowMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SequencedTradeNowMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequencedTradeNowMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SequencedTradeNowMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | acceptedMessage (message : AcceptedMessage) -- 'A' 0x41
  | replacedMessage (message : ReplacedMessage) -- 'U' 0x55
  | canceledMessage (message : CanceledMessage) -- 'C' 0x43
  | aiqCancelledMessage (message : AiqCancelledMessage) -- 'D' 0x44
  | executedMessage (message : ExecutedMessage) -- 'E' 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- 'B' 0x42
  | executedWithReferencePriceMessage (message : ExecutedWithReferencePriceMessage) -- 'G' 0x47
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- 'F' 0x46
  | rejectedOrderMessage (message : RejectedOrderMessage) -- 'J' 0x4A
  | cancelPendingMessage (message : CancelPendingMessage) -- 'P' 0x50
  | cancelRejectMessage (message : CancelRejectMessage) -- 'I' 0x49
  | orderPriorityUpdateMessage (message : OrderPriorityUpdateMessage) -- 'T' 0x54
  | orderModifiedMessage (message : OrderModifiedMessage) -- 'M' 0x4D
  | sequencedTradeNowMessage (message : SequencedTradeNowMessage) -- 'N' 0x4E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .acceptedMessage _ => 65
  | .replacedMessage _ => 85
  | .canceledMessage _ => 67
  | .aiqCancelledMessage _ => 68
  | .executedMessage _ => 69
  | .brokenTradeMessage _ => 66
  | .executedWithReferencePriceMessage _ => 71
  | .tradeCorrectionMessage _ => 70
  | .rejectedOrderMessage _ => 74
  | .cancelPendingMessage _ => 80
  | .cancelRejectMessage _ => 73
  | .orderPriorityUpdateMessage _ => 84
  | .orderModifiedMessage _ => 77
  | .sequencedTradeNowMessage _ => 78

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .acceptedMessage message => AcceptedMessage.encode message
  | .replacedMessage message => ReplacedMessage.encode message
  | .canceledMessage message => CanceledMessage.encode message
  | .aiqCancelledMessage message => AiqCancelledMessage.encode message
  | .executedMessage message => ExecutedMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .executedWithReferencePriceMessage message => ExecutedWithReferencePriceMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .cancelPendingMessage message => CancelPendingMessage.encode message
  | .cancelRejectMessage message => CancelRejectMessage.encode message
  | .orderPriorityUpdateMessage message => OrderPriorityUpdateMessage.encode message
  | .orderModifiedMessage message => OrderModifiedMessage.encode message
  | .sequencedTradeNowMessage message => SequencedTradeNowMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 79 := by
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
  | aiqCancelledMessage inner =>
    simp only [encode, AiqCancelledMessage.encode_length]
    omega
  | executedMessage inner =>
    simp only [encode, ExecutedMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | executedWithReferencePriceMessage inner =>
    simp only [encode, ExecutedWithReferencePriceMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [encode, RejectedOrderMessage.encode_length]
    omega
  | cancelPendingMessage inner =>
    simp only [encode, CancelPendingMessage.encode_length]
    omega
  | cancelRejectMessage inner =>
    simp only [encode, CancelRejectMessage.encode_length]
    omega
  | orderPriorityUpdateMessage inner =>
    simp only [encode, OrderPriorityUpdateMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [encode, OrderModifiedMessage.encode_length]
    omega
  | sequencedTradeNowMessage inner =>
    simp only [encode, SequencedTradeNowMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AcceptedMessage.decode bytes).map fun (message, rest) => (.acceptedMessage message, rest)
  else if tag = 85 then (ReplacedMessage.decode bytes).map fun (message, rest) => (.replacedMessage message, rest)
  else if tag = 67 then (CanceledMessage.decode bytes).map fun (message, rest) => (.canceledMessage message, rest)
  else if tag = 68 then (AiqCancelledMessage.decode bytes).map fun (message, rest) => (.aiqCancelledMessage message, rest)
  else if tag = 69 then (ExecutedMessage.decode bytes).map fun (message, rest) => (.executedMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 71 then (ExecutedWithReferencePriceMessage.decode bytes).map fun (message, rest) => (.executedWithReferencePriceMessage message, rest)
  else if tag = 70 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun (message, rest) => (.rejectedOrderMessage message, rest)
  else if tag = 80 then (CancelPendingMessage.decode bytes).map fun (message, rest) => (.cancelPendingMessage message, rest)
  else if tag = 73 then (CancelRejectMessage.decode bytes).map fun (message, rest) => (.cancelRejectMessage message, rest)
  else if tag = 84 then (OrderPriorityUpdateMessage.decode bytes).map fun (message, rest) => (.orderPriorityUpdateMessage message, rest)
  else if tag = 77 then (OrderModifiedMessage.decode bytes).map fun (message, rest) => (.orderModifiedMessage message, rest)
  else if tag = 78 then (SequencedTradeNowMessage.decode bytes).map fun (message, rest) => (.sequencedTradeNowMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 80 := by
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
  | aiqCancelledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AiqCancelledMessage.encode_length]
    omega
  | executedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutedMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | executedWithReferencePriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutedWithReferencePriceMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RejectedOrderMessage.encode_length]
    omega
  | cancelPendingMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelPendingMessage.encode_length]
    omega
  | cancelRejectMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelRejectMessage.encode_length]
    omega
  | orderPriorityUpdateMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderPriorityUpdateMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderModifiedMessage.encode_length]
    omega
  | sequencedTradeNowMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SequencedTradeNowMessage.encode_length]
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
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- 'A' 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- 'J' 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- 'S' 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- 'H' 0x48
  | endOfSession (message : EndOfSession) -- 'Z' 0x5A
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 80 := by
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

end Omi.NasdaqNsmequitiesOrdersOuchV42Server
