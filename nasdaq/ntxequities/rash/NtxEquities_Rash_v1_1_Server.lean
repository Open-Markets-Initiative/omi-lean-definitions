import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Rash v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxequitiesRashAsciirashV11Server

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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | short -- Short
  | shortExempt -- Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .short => 0x54
  | .shortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .short
  else .shortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | short => decide
  | shortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59, 0x4E, 0x41, 0x49, 0x50, 0x57, 0x4D, 0x4F, 0x54, 0x51, 0x52, 0x64]

inductive Display where
  | anonymousPriceToComply -- Anonymous Price To Comply
  | nonDisplayed -- Non Displayed
  | attributablePriceToDisplay -- Attributable Price To Display
  | imbalanceOnly -- Imbalance Only
  | postOnly -- Post Only
  | midPointPegPostOnly -- Mid Point Peg Post Only
  | midPointPeg -- Mid Point Peg
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovementOrderRpii -- Retail Price Improvement Order Rpii
  | retailPriceImprovementOrderNoRpii -- Retail Price Improvement Order No Rpii
  | directListingCapitalRaise -- Direct Listing Capital Raise
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .anonymousPriceToComply => 0x59
  | .nonDisplayed => 0x4E
  | .attributablePriceToDisplay => 0x41
  | .imbalanceOnly => 0x49
  | .postOnly => 0x50
  | .midPointPegPostOnly => 0x57
  | .midPointPeg => 0x4D
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovementOrderRpii => 0x51
  | .retailPriceImprovementOrderNoRpii => 0x52
  | .directListingCapitalRaise => 0x64
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .anonymousPriceToComply
  else if byte = 0x4E then .nonDisplayed
  else if byte = 0x41 then .attributablePriceToDisplay
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x50 then .postOnly
  else if byte = 0x57 then .midPointPegPostOnly
  else if byte = 0x4D then .midPointPeg
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else if byte = 0x51 then .retailPriceImprovementOrderRpii
  else if byte = 0x52 then .retailPriceImprovementOrderNoRpii
  else .directListingCapitalRaise

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | anonymousPriceToComply => decide
  | nonDisplayed => decide
  | attributablePriceToDisplay => decide
  | imbalanceOnly => decide
  | postOnly => decide
  | midPointPegPostOnly => decide
  | midPointPeg => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovementOrderRpii => decide
  | retailPriceImprovementOrderNoRpii => decide
  | directListingCapitalRaise => decide
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

/-- Peg Type: one byte code -/
def PegType.codes : List UInt8 :=
  [0x4D, 0x4E, 0x50, 0x52]

inductive PegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | unlisted (byte : { byte : UInt8 // byte ∉ PegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegType

def toByte : PegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else .primary

def ofByte (byte : UInt8) : PegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegType

/-- Peg Difference Sign: one byte code -/
def PegDifferenceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive PegDifferenceSign where
  | plus -- Plus
  | minus -- Minus
  | unlisted (byte : { byte : UInt8 // byte ∉ PegDifferenceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegDifferenceSign

def toByte : PegDifferenceSign → UInt8
  | .plus => 0x2B
  | .minus => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegDifferenceSign :=
  if byte = 0x2B then .plus
  else .minus

def ofByte (byte : UInt8) : PegDifferenceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegDifferenceSign) : ofByte value.toByte = value := by
  cases value with
  | plus => decide
  | minus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegDifferenceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegDifferenceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegDifferenceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegDifferenceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegDifferenceSign

/-- Discretion Peg Type: one byte code -/
def DiscretionPegType.codes : List UInt8 :=
  [0x4D, 0x4E, 0x50, 0x52]

inductive DiscretionPegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPegType

def toByte : DiscretionPegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else .primary

def ofByte (byte : UInt8) : DiscretionPegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DiscretionPegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DiscretionPegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DiscretionPegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DiscretionPegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DiscretionPegType

/-- Discretion Peg Difference Sign: one byte code -/
def DiscretionPegDifferenceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive DiscretionPegDifferenceSign where
  | plus -- Plus
  | minus -- Minus
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPegDifferenceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPegDifferenceSign

def toByte : DiscretionPegDifferenceSign → UInt8
  | .plus => 0x2B
  | .minus => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPegDifferenceSign :=
  if byte = 0x2B then .plus
  else .minus

def ofByte (byte : UInt8) : DiscretionPegDifferenceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPegDifferenceSign) : ofByte value.toByte = value := by
  cases value with
  | plus => decide
  | minus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DiscretionPegDifferenceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DiscretionPegDifferenceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DiscretionPegDifferenceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DiscretionPegDifferenceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DiscretionPegDifferenceSign

/-- Intermarket Sweep Eligibility: one byte code -/
def IntermarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E, 0x79]

inductive IntermarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | tradeAtIntermarketSweepOrder -- Trade At Intermarket Sweep Order
  | unlisted (byte : { byte : UInt8 // byte ∉ IntermarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IntermarketSweepEligibility

def toByte : IntermarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .tradeAtIntermarketSweepOrder => 0x79
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IntermarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else if byte = 0x4E then .notEligible
  else .tradeAtIntermarketSweepOrder

def ofByte (byte : UInt8) : IntermarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IntermarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | tradeAtIntermarketSweepOrder => decide
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
  [0x4F, 0x43, 0x4E, 0x52]

inductive CrossType where
  | openingCross -- Opening Cross
  | closingCross -- Closing Cross
  | immediatelyLive -- Immediately Live
  | retailCross -- Retail Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingCross => 0x4F
  | .closingCross => 0x43
  | .immediatelyLive => 0x4E
  | .retailCross => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x4E then .immediatelyLive
  else .retailCross

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingCross => decide
  | closingCross => decide
  | immediatelyLive => decide
  | retailCross => decide
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

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x5A, 0x4B, 0x45, 0x4A, 0x41]

inductive CancelReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrCancel -- Immediate Or Cancel
  | timeout -- Timeout
  | supervisory -- Supervisory
  | regulatoryRestriction -- Regulatory Restriction
  | selfMatchPrevention -- Self Match Prevention
  | systemCancel -- System Cancel
  | marketCollars -- Market Collars
  | closed -- Closed
  | rejectedByAwayDestination -- Rejected By Away Destination
  | administrativeCancel -- Administrative Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .userRequestedCancel => 0x55
  | .immediateOrCancel => 0x49
  | .timeout => 0x54
  | .supervisory => 0x53
  | .regulatoryRestriction => 0x44
  | .selfMatchPrevention => 0x51
  | .systemCancel => 0x5A
  | .marketCollars => 0x4B
  | .closed => 0x45
  | .rejectedByAwayDestination => 0x4A
  | .administrativeCancel => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrCancel
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisory
  else if byte = 0x44 then .regulatoryRestriction
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x5A then .systemCancel
  else if byte = 0x4B then .marketCollars
  else if byte = 0x45 then .closed
  else if byte = 0x4A then .rejectedByAwayDestination
  else .administrativeCancel

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | immediateOrCancel => decide
  | timeout => decide
  | supervisory => decide
  | regulatoryRestriction => decide
  | selfMatchPrevention => decide
  | systemCancel => decide
  | marketCollars => decide
  | closed => decide
  | rejectedByAwayDestination => decide
  | administrativeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Reject Reason: one byte code -/
def RejectReason.codes : List UInt8 :=
  [0x61, 0x41, 0x62, 0x42, 0x43, 0x64, 0x44, 0x65, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x6C, 0x4C, 0x4D, 0x6E, 0x4E, 0x6F, 0x4F, 0x50, 0x71, 0x51, 0x72, 0x52, 0x73, 0x53, 0x75, 0x55, 0x54, 0x76, 0x56, 0x77, 0x57, 0x78, 0x58, 0x79, 0x59, 0x5A]

inductive RejectReason where
  | riskRestrictedStock -- Risk Restricted Stock
  | advanceFeaturesNotAllowed -- Advance Features Not Allowed
  | riskShortSellRestricted -- Risk Short Sell Restricted
  | quoteNotAvailableForPeggedOrder -- Quote Not Available For Pegged Order
  | nasdaqTexasIsClosed -- Nasdaq Texas Is Closed
  | riskExceedsAdvLimit -- Risk Exceeds Adv Limit
  | invalidDisplayValue -- Invalid Display Value
  | riskFatFinger -- Risk Fat Finger
  | invalidPeg -- Invalid Peg
  | orderNotMarketable -- Order Not Marketable
  | destinationNotAvailable -- Destination Not Available
  | securityIsHalted -- Security Is Halted
  | invalidOrderSide -- Invalid Order Side
  | processingError -- Processing Error
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | riskLocateRequired -- Risk Locate Required
  | invalidFirm -- Invalid Firm
  | outsideOfPermittedTimesForClearingDestination -- Outside Of Permitted Times For Clearing Destination
  | riskMaxNotionalExceeded -- Risk Max Notional Exceeded
  | invalidRoutingInstructions -- Invalid Routing Instructions
  | riskOrderTypeRestricted -- Risk Order Type Restricted
  | other -- Other
  | peggingNotAllowed -- Pegging Not Allowed
  | invalidOrderQuantity -- Invalid Order Quantity
  | midpointPegNotAcceptedInCrossedMarket -- Midpoint Peg Not Accepted In Crossed Market
  | riskMarketImpact -- Risk Market Impact
  | routingNotAllowed -- Routing Not Allowed
  | riskOpenExposureExceeded -- Risk Open Exposure Exceeded
  | invalidSymbol -- Invalid Symbol
  | riskPortMessageRateExceeded -- Risk Port Message Rate Exceeded
  | possibleDuplicateOrder -- Possible Duplicate Order
  | testMode -- Test Mode
  | riskSymbolMessageRateExceeded -- Risk Symbol Message Rate Exceeded
  | invalidOrderType -- Invalid Order Type
  | riskDuplicateMessageRateExceeded -- Risk Duplicate Message Rate Exceeded
  | invalidDestination -- Invalid Destination
  | riskExecutedExposureExceeded -- Risk Executed Exposure Exceeded
  | invalidPrice -- Invalid Price
  | riskNotionalExposureExceeded -- Risk Notional Exposure Exceeded
  | noSharesFoundForRouting -- No Shares Found For Routing
  | quantityExceedsThreshold -- Quantity Exceeds Threshold
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReason

def toByte : RejectReason → UInt8
  | .riskRestrictedStock => 0x61
  | .advanceFeaturesNotAllowed => 0x41
  | .riskShortSellRestricted => 0x62
  | .quoteNotAvailableForPeggedOrder => 0x42
  | .nasdaqTexasIsClosed => 0x43
  | .riskExceedsAdvLimit => 0x64
  | .invalidDisplayValue => 0x44
  | .riskFatFinger => 0x65
  | .invalidPeg => 0x45
  | .orderNotMarketable => 0x46
  | .destinationNotAvailable => 0x47
  | .securityIsHalted => 0x48
  | .invalidOrderSide => 0x49
  | .processingError => 0x4A
  | .invalidMinimumQuantity => 0x4B
  | .riskLocateRequired => 0x6C
  | .invalidFirm => 0x4C
  | .outsideOfPermittedTimesForClearingDestination => 0x4D
  | .riskMaxNotionalExceeded => 0x6E
  | .invalidRoutingInstructions => 0x4E
  | .riskOrderTypeRestricted => 0x6F
  | .other => 0x4F
  | .peggingNotAllowed => 0x50
  | .invalidOrderQuantity => 0x71
  | .midpointPegNotAcceptedInCrossedMarket => 0x51
  | .riskMarketImpact => 0x72
  | .routingNotAllowed => 0x52
  | .riskOpenExposureExceeded => 0x73
  | .invalidSymbol => 0x53
  | .riskPortMessageRateExceeded => 0x75
  | .possibleDuplicateOrder => 0x55
  | .testMode => 0x54
  | .riskSymbolMessageRateExceeded => 0x76
  | .invalidOrderType => 0x56
  | .riskDuplicateMessageRateExceeded => 0x77
  | .invalidDestination => 0x57
  | .riskExecutedExposureExceeded => 0x78
  | .invalidPrice => 0x58
  | .riskNotionalExposureExceeded => 0x79
  | .noSharesFoundForRouting => 0x59
  | .quantityExceedsThreshold => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReason :=
  if byte = 0x61 then .riskRestrictedStock
  else if byte = 0x41 then .advanceFeaturesNotAllowed
  else if byte = 0x62 then .riskShortSellRestricted
  else if byte = 0x42 then .quoteNotAvailableForPeggedOrder
  else if byte = 0x43 then .nasdaqTexasIsClosed
  else if byte = 0x64 then .riskExceedsAdvLimit
  else if byte = 0x44 then .invalidDisplayValue
  else if byte = 0x65 then .riskFatFinger
  else if byte = 0x45 then .invalidPeg
  else if byte = 0x46 then .orderNotMarketable
  else if byte = 0x47 then .destinationNotAvailable
  else if byte = 0x48 then .securityIsHalted
  else if byte = 0x49 then .invalidOrderSide
  else if byte = 0x4A then .processingError
  else if byte = 0x4B then .invalidMinimumQuantity
  else if byte = 0x6C then .riskLocateRequired
  else if byte = 0x4C then .invalidFirm
  else if byte = 0x4D then .outsideOfPermittedTimesForClearingDestination
  else if byte = 0x6E then .riskMaxNotionalExceeded
  else if byte = 0x4E then .invalidRoutingInstructions
  else if byte = 0x6F then .riskOrderTypeRestricted
  else if byte = 0x4F then .other
  else if byte = 0x50 then .peggingNotAllowed
  else if byte = 0x71 then .invalidOrderQuantity
  else if byte = 0x51 then .midpointPegNotAcceptedInCrossedMarket
  else if byte = 0x72 then .riskMarketImpact
  else if byte = 0x52 then .routingNotAllowed
  else if byte = 0x73 then .riskOpenExposureExceeded
  else if byte = 0x53 then .invalidSymbol
  else if byte = 0x75 then .riskPortMessageRateExceeded
  else if byte = 0x55 then .possibleDuplicateOrder
  else if byte = 0x54 then .testMode
  else if byte = 0x76 then .riskSymbolMessageRateExceeded
  else if byte = 0x56 then .invalidOrderType
  else if byte = 0x77 then .riskDuplicateMessageRateExceeded
  else if byte = 0x57 then .invalidDestination
  else if byte = 0x78 then .riskExecutedExposureExceeded
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x79 then .riskNotionalExposureExceeded
  else if byte = 0x59 then .noSharesFoundForRouting
  else .quantityExceedsThreshold

def ofByte (byte : UInt8) : RejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReason) : ofByte value.toByte = value := by
  cases value with
  | riskRestrictedStock => decide
  | advanceFeaturesNotAllowed => decide
  | riskShortSellRestricted => decide
  | quoteNotAvailableForPeggedOrder => decide
  | nasdaqTexasIsClosed => decide
  | riskExceedsAdvLimit => decide
  | invalidDisplayValue => decide
  | riskFatFinger => decide
  | invalidPeg => decide
  | orderNotMarketable => decide
  | destinationNotAvailable => decide
  | securityIsHalted => decide
  | invalidOrderSide => decide
  | processingError => decide
  | invalidMinimumQuantity => decide
  | riskLocateRequired => decide
  | invalidFirm => decide
  | outsideOfPermittedTimesForClearingDestination => decide
  | riskMaxNotionalExceeded => decide
  | invalidRoutingInstructions => decide
  | riskOrderTypeRestricted => decide
  | other => decide
  | peggingNotAllowed => decide
  | invalidOrderQuantity => decide
  | midpointPegNotAcceptedInCrossedMarket => decide
  | riskMarketImpact => decide
  | routingNotAllowed => decide
  | riskOpenExposureExceeded => decide
  | invalidSymbol => decide
  | riskPortMessageRateExceeded => decide
  | possibleDuplicateOrder => decide
  | testMode => decide
  | riskSymbolMessageRateExceeded => decide
  | invalidOrderType => decide
  | riskDuplicateMessageRateExceeded => decide
  | invalidDestination => decide
  | riskExecutedExposureExceeded => decide
  | invalidPrice => decide
  | riskNotionalExposureExceeded => decide
  | noSharesFoundForRouting => decide
  | quantityExceedsThreshold => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReason

/-- Liquidity: one byte code -/
def Liquidity.codes : List UInt8 :=
  [0x41, 0x52, 0x4A, 0x58, 0x44, 0x46, 0x47, 0x59, 0x53, 0x55, 0x45, 0x50, 0x54, 0x5A, 0x51, 0x6D, 0x6B, 0x6A, 0x72, 0x74, 0x71, 0x34, 0x36, 0x37, 0x38, 0x70, 0x4E, 0x31, 0x75]

inductive Liquidity where
  | added -- Added
  | removed -- Removed
  | nonDisplayedAndAddedLiquidity -- Non Displayed And Added Liquidity
  | routed -- Routed
  | dot -- Dot
  | addedOrOpeningTrade -- Added Or Opening Trade
  | oddLotOrOnCloseOrder -- Odd Lot Or On Close Order
  | reRoutedByNyse -- Re Routed By Nyse
  | oddLotExecution -- Odd Lot Execution
  | addedLiquidity -- Added Liquidity
  | nyseOther -- Nyse Other
  | routedToPsx -- Routed To Psx
  | openingTrade -- Opening Trade
  | onCloseOrder -- On Close Order
  | routedToNasdaq -- Routed To Nasdaq
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | rpiOrderProvidesLiquidityRetailPriceImprovementIndicator -- Rpi Order Provides Liquidity Retail Price Improvement Indicator
  | rmoRetailOrderRemovesRpiLiquidity -- Rmo Retail Order Removes Rpi Liquidity
  | rmoRetailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity -- Rmo Retail Order Removes Price Improving Non Displayed Liquidity Other Than Rpi Liquidity
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity -- Rmo Retail Order Removes Non Rpi Midpoint Liquidity
  | rpiOrderProvidesLiquidityExecutesAgainstRmoOrderWithNotional10000 -- Rpi Order Provides Liquidity Executes Against Rmo Order With Notional 10000
  | rmoOrderRemovesRpiLiquidityNotional10000 -- Rmo Order Removes Rpi Liquidity Notional 10000
  | displayedLiquidityAddingOrderImprovesTheNbbo -- Displayed Liquidity Adding Order Improves The Nbbo
  | displayedLiquidityAddingOrderSetsTheNtxbboWhileJoiningTheNbbo -- Displayed Liquidity Adding Order Sets The Ntxbbo While Joining The Nbbo
  | removedPriceImprovingNonDisplayedLiquidity -- Removed Price Improving Non Displayed Liquidity
  | passiveMidpointExecution -- Passive Midpoint Execution
  | rpiOrderProvidesLiquidityNoRpii -- Rpi Order Provides Liquidity No Rpii
  | addedNonDisplayedLiquidityViaAReserveOrder -- Added Non Displayed Liquidity Via A Reserve Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Liquidity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Liquidity

def toByte : Liquidity → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .nonDisplayedAndAddedLiquidity => 0x4A
  | .routed => 0x58
  | .dot => 0x44
  | .addedOrOpeningTrade => 0x46
  | .oddLotOrOnCloseOrder => 0x47
  | .reRoutedByNyse => 0x59
  | .oddLotExecution => 0x53
  | .addedLiquidity => 0x55
  | .nyseOther => 0x45
  | .routedToPsx => 0x50
  | .openingTrade => 0x54
  | .onCloseOrder => 0x5A
  | .routedToNasdaq => 0x51
  | .removedLiquidityAtAMidpoint => 0x6D
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .rpiOrderProvidesLiquidityRetailPriceImprovementIndicator => 0x6A
  | .rmoRetailOrderRemovesRpiLiquidity => 0x72
  | .rmoRetailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity => 0x74
  | .rmoRetailOrderRemovesNonRpiMidpointLiquidity => 0x71
  | .rpiOrderProvidesLiquidityExecutesAgainstRmoOrderWithNotional10000 => 0x34
  | .rmoOrderRemovesRpiLiquidityNotional10000 => 0x36
  | .displayedLiquidityAddingOrderImprovesTheNbbo => 0x37
  | .displayedLiquidityAddingOrderSetsTheNtxbboWhileJoiningTheNbbo => 0x38
  | .removedPriceImprovingNonDisplayedLiquidity => 0x70
  | .passiveMidpointExecution => 0x4E
  | .rpiOrderProvidesLiquidityNoRpii => 0x31
  | .addedNonDisplayedLiquidityViaAReserveOrder => 0x75
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Liquidity :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x4A then .nonDisplayedAndAddedLiquidity
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dot
  else if byte = 0x46 then .addedOrOpeningTrade
  else if byte = 0x47 then .oddLotOrOnCloseOrder
  else if byte = 0x59 then .reRoutedByNyse
  else if byte = 0x53 then .oddLotExecution
  else if byte = 0x55 then .addedLiquidity
  else if byte = 0x45 then .nyseOther
  else if byte = 0x50 then .routedToPsx
  else if byte = 0x54 then .openingTrade
  else if byte = 0x5A then .onCloseOrder
  else if byte = 0x51 then .routedToNasdaq
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else if byte = 0x6B then .addedLiquidityViaAMidpointOrder
  else if byte = 0x6A then .rpiOrderProvidesLiquidityRetailPriceImprovementIndicator
  else if byte = 0x72 then .rmoRetailOrderRemovesRpiLiquidity
  else if byte = 0x74 then .rmoRetailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity
  else if byte = 0x71 then .rmoRetailOrderRemovesNonRpiMidpointLiquidity
  else if byte = 0x34 then .rpiOrderProvidesLiquidityExecutesAgainstRmoOrderWithNotional10000
  else if byte = 0x36 then .rmoOrderRemovesRpiLiquidityNotional10000
  else if byte = 0x37 then .displayedLiquidityAddingOrderImprovesTheNbbo
  else if byte = 0x38 then .displayedLiquidityAddingOrderSetsTheNtxbboWhileJoiningTheNbbo
  else if byte = 0x70 then .removedPriceImprovingNonDisplayedLiquidity
  else if byte = 0x4E then .passiveMidpointExecution
  else if byte = 0x31 then .rpiOrderProvidesLiquidityNoRpii
  else .addedNonDisplayedLiquidityViaAReserveOrder

def ofByte (byte : UInt8) : Liquidity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Liquidity) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | nonDisplayedAndAddedLiquidity => decide
  | routed => decide
  | dot => decide
  | addedOrOpeningTrade => decide
  | oddLotOrOnCloseOrder => decide
  | reRoutedByNyse => decide
  | oddLotExecution => decide
  | addedLiquidity => decide
  | nyseOther => decide
  | routedToPsx => decide
  | openingTrade => decide
  | onCloseOrder => decide
  | routedToNasdaq => decide
  | removedLiquidityAtAMidpoint => decide
  | addedLiquidityViaAMidpointOrder => decide
  | rpiOrderProvidesLiquidityRetailPriceImprovementIndicator => decide
  | rmoRetailOrderRemovesRpiLiquidity => decide
  | rmoRetailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity => decide
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity => decide
  | rpiOrderProvidesLiquidityExecutesAgainstRmoOrderWithNotional10000 => decide
  | rmoOrderRemovesRpiLiquidityNotional10000 => decide
  | displayedLiquidityAddingOrderImprovesTheNbbo => decide
  | displayedLiquidityAddingOrderSetsTheNtxbboWhileJoiningTheNbbo => decide
  | removedPriceImprovingNonDisplayedLiquidity => decide
  | passiveMidpointExecution => decide
  | rpiOrderProvidesLiquidityNoRpii => decide
  | addedNonDisplayedLiquidityViaAReserveOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Liquidity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Liquidity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Liquidity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Liquidity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Liquidity

/-- Broken Trade Reason: one byte code -/
def BrokenTradeReason.codes : List UInt8 :=
  [0x45, 0x43, 0x53, 0x58]

inductive BrokenTradeReason where
  | erroneous -- Erroneous
  | consent -- Consent
  | supervisory -- Supervisory
  | external -- External
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokenTradeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokenTradeReason

def toByte : BrokenTradeReason → UInt8
  | .erroneous => 0x45
  | .consent => 0x43
  | .supervisory => 0x53
  | .external => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokenTradeReason :=
  if byte = 0x45 then .erroneous
  else if byte = 0x43 then .consent
  else if byte = 0x53 then .supervisory
  else .external

def ofByte (byte : UInt8) : BrokenTradeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokenTradeReason) : ofByte value.toByte = value := by
  cases value with
  | erroneous => decide
  | consent => decide
  | supervisory => decide
  | external => decide
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

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65376
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65376 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65376 := by
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

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Accepted Order Message: 147 bytes -/
structure AcceptedOrderMessage where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 8
  price : Alpha 10
  timeInForce : Alpha 5
  firmClientId : Alpha 4
  display : Display
  orderReferenceNumber : Alpha 9
  minQty : Alpha 6
  maxFloor : Alpha 6
  pegType : PegType
  pegDifferenceSign : PegDifferenceSign
  pegDifference : Alpha 10
  discretionPrice : Alpha 10
  discretionPegType : DiscretionPegType
  discretionPegDifferenceSign : DiscretionPegDifferenceSign
  discretionPegDifference : Alpha 10
  capacityRule80AIndicator : Alpha 1
  randomReserve : Alpha 6
  routeDestExecBroker : Alpha 4
  custTerminalIdSenderSubId : Alpha 32
  deriving DecidableEq, Repr

namespace AcceptedOrderMessage

def encode (message : AcceptedOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.sharesOrderQty
    ++ (Alpha.encode message.stockSymbol
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.firmClientId
    ++ (Display.encode message.display
    ++ (Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.minQty
    ++ (Alpha.encode message.maxFloor
    ++ (PegType.encode message.pegType
    ++ (PegDifferenceSign.encode message.pegDifferenceSign
    ++ (Alpha.encode message.pegDifference
    ++ (Alpha.encode message.discretionPrice
    ++ (DiscretionPegType.encode message.discretionPegType
    ++ (DiscretionPegDifferenceSign.encode message.discretionPegDifferenceSign
    ++ (Alpha.encode message.discretionPegDifference
    ++ (Alpha.encode message.capacityRule80AIndicator
    ++ (Alpha.encode message.randomReserve
    ++ (Alpha.encode message.routeDestExecBroker
    ++ (Alpha.encode message.custTerminalIdSenderSubId)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (AcceptedOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← Alpha.decode 5 bytes
  let (firmClientId, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (minQty, bytes) ← Alpha.decode 6 bytes
  let (maxFloor, bytes) ← Alpha.decode 6 bytes
  let (pegType, bytes) ← PegType.decode bytes
  let (pegDifferenceSign, bytes) ← PegDifferenceSign.decode bytes
  let (pegDifference, bytes) ← Alpha.decode 10 bytes
  let (discretionPrice, bytes) ← Alpha.decode 10 bytes
  let (discretionPegType, bytes) ← DiscretionPegType.decode bytes
  let (discretionPegDifferenceSign, bytes) ← DiscretionPegDifferenceSign.decode bytes
  let (discretionPegDifference, bytes) ← Alpha.decode 10 bytes
  let (capacityRule80AIndicator, bytes) ← Alpha.decode 1 bytes
  let (randomReserve, bytes) ← Alpha.decode 6 bytes
  let (routeDestExecBroker, bytes) ← Alpha.decode 4 bytes
  let (custTerminalIdSenderSubId, bytes) ← Alpha.decode 32 bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, orderReferenceNumber, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId }, bytes)

@[simp] theorem encode_length (message : AcceptedOrderMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length]

theorem encode_length_pos (message : AcceptedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AcceptedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AcceptedOrderMessage

/-- Accepted Order Message With Cross Functionality: 149 bytes -/
structure AcceptedOrderMessageWithCrossFunctionality where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 8
  price : Alpha 10
  timeInForce : Alpha 5
  firmClientId : Alpha 4
  display : Display
  orderReferenceNumber : Alpha 9
  minQty : Alpha 6
  maxFloor : Alpha 6
  pegType : PegType
  pegDifferenceSign : PegDifferenceSign
  pegDifference : Alpha 10
  discretionPrice : Alpha 10
  discretionPegType : DiscretionPegType
  discretionPegDifferenceSign : DiscretionPegDifferenceSign
  discretionPegDifference : Alpha 10
  capacityRule80AIndicator : Alpha 1
  randomReserve : Alpha 6
  routeDestExecBroker : Alpha 4
  custTerminalIdSenderSubId : Alpha 32
  intermarketSweepEligibility : IntermarketSweepEligibility
  crossType : CrossType
  deriving DecidableEq, Repr

namespace AcceptedOrderMessageWithCrossFunctionality

def encode (message : AcceptedOrderMessageWithCrossFunctionality) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.sharesOrderQty
    ++ (Alpha.encode message.stockSymbol
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.firmClientId
    ++ (Display.encode message.display
    ++ (Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.minQty
    ++ (Alpha.encode message.maxFloor
    ++ (PegType.encode message.pegType
    ++ (PegDifferenceSign.encode message.pegDifferenceSign
    ++ (Alpha.encode message.pegDifference
    ++ (Alpha.encode message.discretionPrice
    ++ (DiscretionPegType.encode message.discretionPegType
    ++ (DiscretionPegDifferenceSign.encode message.discretionPegDifferenceSign
    ++ (Alpha.encode message.discretionPegDifference
    ++ (Alpha.encode message.capacityRule80AIndicator
    ++ (Alpha.encode message.randomReserve
    ++ (Alpha.encode message.routeDestExecBroker
    ++ (Alpha.encode message.custTerminalIdSenderSubId
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (CrossType.encode message.crossType)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (AcceptedOrderMessageWithCrossFunctionality × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← Alpha.decode 5 bytes
  let (firmClientId, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (minQty, bytes) ← Alpha.decode 6 bytes
  let (maxFloor, bytes) ← Alpha.decode 6 bytes
  let (pegType, bytes) ← PegType.decode bytes
  let (pegDifferenceSign, bytes) ← PegDifferenceSign.decode bytes
  let (pegDifference, bytes) ← Alpha.decode 10 bytes
  let (discretionPrice, bytes) ← Alpha.decode 10 bytes
  let (discretionPegType, bytes) ← DiscretionPegType.decode bytes
  let (discretionPegDifferenceSign, bytes) ← DiscretionPegDifferenceSign.decode bytes
  let (discretionPegDifference, bytes) ← Alpha.decode 10 bytes
  let (capacityRule80AIndicator, bytes) ← Alpha.decode 1 bytes
  let (randomReserve, bytes) ← Alpha.decode 6 bytes
  let (routeDestExecBroker, bytes) ← Alpha.decode 4 bytes
  let (custTerminalIdSenderSubId, bytes) ← Alpha.decode 32 bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, orderReferenceNumber, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId, intermarketSweepEligibility, crossType }, bytes)

@[simp] theorem encode_length (message : AcceptedOrderMessageWithCrossFunctionality) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : AcceptedOrderMessageWithCrossFunctionality) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AcceptedOrderMessageWithCrossFunctionality) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [CrossType.decode_encode, some_bind]
  rfl

end AcceptedOrderMessageWithCrossFunctionality

/-- Canceled Order Message: 21 bytes -/
structure CanceledOrderMessage where
  orderTokenClientOrderId : Alpha 14
  shares : Alpha 6
  cancelReason : CancelReason
  deriving DecidableEq, Repr

namespace CanceledOrderMessage

def encode (message : CanceledOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Alpha.encode message.shares
    ++ (CancelReason.encode message.cancelReason))

def decode (bytes : List UInt8) : Option (CanceledOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ orderTokenClientOrderId, shares, cancelReason }, bytes)

@[simp] theorem encode_length (message : CanceledOrderMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CancelReason.encode_length]

theorem encode_length_pos (message : CanceledOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CanceledOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end CanceledOrderMessage

/-- Rejected Order Message: 15 bytes -/
structure RejectedOrderMessage where
  orderTokenClientOrderId : Alpha 14
  rejectReason : RejectReason
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

def encode (message : RejectedOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (RejectReason.encode message.rejectReason)

def decode (bytes : List UInt8) : Option (RejectedOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (rejectReason, bytes) ← RejectReason.decode bytes
  pure ({ orderTokenClientOrderId, rejectReason }, bytes)

@[simp] theorem encode_length (message : RejectedOrderMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RejectReason.encode_length]

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RejectReason.decode_encode, some_bind]
  rfl

end RejectedOrderMessage

/-- Executed Order Message: 40 bytes -/
structure ExecutedOrderMessage where
  orderTokenClientOrderId : Alpha 14
  shares : Alpha 6
  price : Alpha 10
  liquidity : Liquidity
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace ExecutedOrderMessage

def encode (message : ExecutedOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.price
    ++ (Liquidity.encode message.liquidity
    ++ (Alpha.encode message.matchNumber))))

def decode (bytes : List UInt8) : Option (ExecutedOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (liquidity, bytes) ← Liquidity.decode bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ orderTokenClientOrderId, shares, price, liquidity, matchNumber }, bytes)

@[simp] theorem encode_length (message : ExecutedOrderMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Liquidity.encode_length]

theorem encode_length_pos (message : ExecutedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Liquidity.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutedOrderMessage

/-- Broken Trade Message: 24 bytes -/
structure BrokenTradeMessage where
  orderToken : Alpha 14
  matchNumber : Alpha 9
  brokenTradeReason : BrokenTradeReason
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ (Alpha.encode message.matchNumber
    ++ (BrokenTradeReason.encode message.brokenTradeReason))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (brokenTradeReason, bytes) ← BrokenTradeReason.decode bytes
  pure ({ orderToken, matchNumber, brokenTradeReason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BrokenTradeReason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BrokenTradeReason.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | acceptedOrderMessage (message : AcceptedOrderMessage) -- "A" 0x41
  | acceptedOrderMessageWithCrossFunctionality (message : AcceptedOrderMessageWithCrossFunctionality) -- "R" 0x52
  | canceledOrderMessage (message : CanceledOrderMessage) -- "C" 0x43
  | rejectedOrderMessage (message : RejectedOrderMessage) -- "J" 0x4A
  | executedOrderMessage (message : ExecutedOrderMessage) -- "E" 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .acceptedOrderMessage _ => 65
  | .acceptedOrderMessageWithCrossFunctionality _ => 82
  | .canceledOrderMessage _ => 67
  | .rejectedOrderMessage _ => 74
  | .executedOrderMessage _ => 69
  | .brokenTradeMessage _ => 66

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .acceptedOrderMessage message => AcceptedOrderMessage.encode message
  | .acceptedOrderMessageWithCrossFunctionality message => AcceptedOrderMessageWithCrossFunctionality.encode message
  | .canceledOrderMessage message => CanceledOrderMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .executedOrderMessage message => ExecutedOrderMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 149 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | acceptedOrderMessage inner =>
    simp only [encode, AcceptedOrderMessage.encode_length]
    omega
  | acceptedOrderMessageWithCrossFunctionality inner =>
    simp only [encode, AcceptedOrderMessageWithCrossFunctionality.encode_length]
    omega
  | canceledOrderMessage inner =>
    simp only [encode, CanceledOrderMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [encode, RejectedOrderMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [encode, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AcceptedOrderMessage.decode bytes).map fun (message, rest) => (.acceptedOrderMessage message, rest)
  else if tag = 82 then (AcceptedOrderMessageWithCrossFunctionality.decode bytes).map fun (message, rest) => (.acceptedOrderMessageWithCrossFunctionality message, rest)
  else if tag = 67 then (CanceledOrderMessage.decode bytes).map fun (message, rest) => (.canceledOrderMessage message, rest)
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun (message, rest) => (.rejectedOrderMessage message, rest)
  else if tag = 69 then (ExecutedOrderMessage.decode bytes).map fun (message, rest) => (.executedOrderMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  timestamp : Alpha 8
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ timestamp, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 158 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | acceptedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AcceptedOrderMessage.encode_length]
    omega
  | acceptedOrderMessageWithCrossFunctionality inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AcceptedOrderMessageWithCrossFunctionality.encode_length]
    omega
  | canceledOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, CanceledOrderMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RejectedOrderMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65376 := by
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

end Omi.NasdaqNtxequitiesRashAsciirashV11Server
