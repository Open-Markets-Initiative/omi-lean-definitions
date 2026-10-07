import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Rash v1.1.2016

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesRashAsciirashV112016Server

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
  [0x59, 0x4E, 0x41, 0x49, 0x50, 0x57, 0x4C, 0x4F, 0x54, 0x51, 0x4D]

inductive Display where
  | anonymousPriceToComply -- Anonymous Price To Comply
  | nonDisplayed -- Non Displayed
  | attributablePriceToDisplay -- Attributable Price To Display
  | imbalanceOnly -- Imbalance Only
  | postOnly -- Post Only
  | midPointPegPostOnly -- Mid Point Peg Post Only
  | postOnlyAndAttributablePriceToDisplay -- Post Only And Attributable Price To Display
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovementOrder -- Retail Price Improvement Order
  | midPointPeg -- Mid Point Peg
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
  | .postOnlyAndAttributablePriceToDisplay => 0x4C
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovementOrder => 0x51
  | .midPointPeg => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .anonymousPriceToComply
  else if byte = 0x4E then .nonDisplayed
  else if byte = 0x41 then .attributablePriceToDisplay
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x50 then .postOnly
  else if byte = 0x57 then .midPointPegPostOnly
  else if byte = 0x4C then .postOnlyAndAttributablePriceToDisplay
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else if byte = 0x51 then .retailPriceImprovementOrder
  else .midPointPeg

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
  | postOnlyAndAttributablePriceToDisplay => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovementOrder => decide
  | midPointPeg => decide
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
  [0x4D, 0x4E, 0x50, 0x52, 0x51, 0x49]

inductive PegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | marketMakerPeg -- Market Maker Peg
  | inavPeg -- Inav Peg
  | unlisted (byte : { byte : UInt8 // byte ∉ PegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegType

def toByte : PegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .marketMakerPeg => 0x51
  | .inavPeg => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else if byte = 0x52 then .primary
  else if byte = 0x51 then .marketMakerPeg
  else .inavPeg

def ofByte (byte : UInt8) : PegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | marketMakerPeg => decide
  | inavPeg => decide
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
  [0x4D, 0x4E, 0x50, 0x52, 0x49]

inductive DiscretionPegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | inavPeg -- Inav Peg
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPegType

def toByte : DiscretionPegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .inavPeg => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else if byte = 0x52 then .primary
  else .inavPeg

def ofByte (byte : UInt8) : DiscretionPegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | inavPeg => decide
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
  [0x59, 0x4E]

inductive IntermarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | unlisted (byte : { byte : UInt8 // byte ∉ IntermarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IntermarketSweepEligibility

def toByte : IntermarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IntermarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else .notEligible

def ofByte (byte : UInt8) : IntermarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IntermarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
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
  [0x4F, 0x43, 0x49, 0x4E, 0x52]

inductive CrossType where
  | openingCross -- Opening Cross
  | closingCross -- Closing Cross
  | intradayCross -- Intraday Cross
  | immediatelyLive -- Immediately Live
  | retailCross -- Retail Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingCross => 0x4F
  | .closingCross => 0x43
  | .intradayCross => 0x49
  | .immediatelyLive => 0x4E
  | .retailCross => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x49 then .intradayCross
  else if byte = 0x4E then .immediatelyLive
  else .retailCross

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingCross => decide
  | closingCross => decide
  | intradayCross => decide
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
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x4B, 0x45, 0x58]

inductive CancelReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrCancel -- Immediate Or Cancel
  | timeout -- Timeout
  | supervisory -- Supervisory
  | regulatoryRestriction -- Regulatory Restriction
  | selfMatchPrevention -- Self Match Prevention
  | marketCollars -- Market Collars
  | closed -- Closed
  | closing -- Closing
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
  | .marketCollars => 0x4B
  | .closed => 0x45
  | .closing => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrCancel
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisory
  else if byte = 0x44 then .regulatoryRestriction
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x4B then .marketCollars
  else if byte = 0x45 then .closed
  else .closing

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
  | marketCollars => decide
  | closed => decide
  | closing => decide
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
  [0x59, 0x43, 0x49, 0x45, 0x4C, 0x5A, 0x4F, 0x42, 0x50, 0x58, 0x47, 0x4A, 0x4E, 0x44, 0x4D, 0x48, 0x53, 0x51, 0x4B, 0x57, 0x41, 0x55, 0x56, 0x54, 0x52, 0x46, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x7B]

inductive RejectReason where
  | noSharesFoundForRouting -- No Shares Found For Routing
  | nasdaqOmxPsxIsClosed -- Nasdaq Omx Psx Is Closed
  | invalidOrderSide -- Invalid Order Side
  | invalidPeg -- Invalid Peg
  | invalidFirm -- Invalid Firm
  | quantityExceedsThreshold -- Quantity Exceeds Threshold
  | other -- Other
  | quoteNotAvailableForPeggedOrder -- Quote Not Available For Pegged Order
  | peggingNotAllowed -- Pegging Not Allowed
  | invalidPrice -- Invalid Price
  | destinationNotAvailable -- Destination Not Available
  | processingError -- Processing Error
  | invalidRoutingInstructions -- Invalid Routing Instructions
  | invalidDisplayValue -- Invalid Display Value
  | outsideOfPermittedTimesForClearingDestination -- Outside Of Permitted Times For Clearing Destination
  | securityIsHalted -- Security Is Halted
  | invalidSymbol -- Invalid Symbol
  | invalidOrderQuantity -- Invalid Order Quantity
  | invalidMinimumQuantity -- Invalid Minimum Quantity
  | invalidDestination -- Invalid Destination
  | advanceFeaturesNotAllowed -- Advance Features Not Allowed
  | possibleDuplicateOrder -- Possible Duplicate Order
  | invalidOrderType -- Invalid Order Type
  | testMode -- Test Mode
  | routingNotAllowed -- Routing Not Allowed
  | orderNotMarketable -- Order Not Marketable
  | prmInvalidMessageFormat -- Prm Invalid Message Format
  | prmNoQuote -- Prm No Quote
  | prmInvalidAccount -- Prm Invalid Account
  | prmShortSaleViolation -- Prm Short Sale Violation
  | prmIsoOrderCheck -- Prm Iso Order Check
  | prmGtcOrderCheck -- Prm Gtc Order Check
  | prmPreMarketOrderCheck -- Prm Pre Market Order Check
  | prmPostMarketOrderCheck -- Prm Post Market Order Check
  | prmDelayedCheckingFlagOff -- Prm Delayed Checking Flag Off
  | prmExceededMaximumSharesThreshold -- Prm Exceeded Maximum Shares Threshold
  | prmExceededMaximumValueThreshold -- Prm Exceeded Maximum Value Threshold
  | prmRejectAllOrders -- Prm Reject All Orders
  | prmInvalidPriceFatFinger -- Prm Invalid Price Fat Finger
  | prmNotOnEasyToBorrowList -- Prm Not On Easy To Borrow List
  | prmNotAvailable -- Prm Not Available
  | prmInvalidMessage -- Prm Invalid Message
  | prmSnapInProcess -- Prm Snap In Process
  | prmSymbolHalted -- Prm Symbol Halted
  | prmOnOpen -- Prm On Open
  | prmOnClose -- Prm On Close
  | prmProgramTrading -- Prm Program Trading
  | prmNotOnRestrictedList -- Prm Not On Restricted List
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReason

def toByte : RejectReason → UInt8
  | .noSharesFoundForRouting => 0x59
  | .nasdaqOmxPsxIsClosed => 0x43
  | .invalidOrderSide => 0x49
  | .invalidPeg => 0x45
  | .invalidFirm => 0x4C
  | .quantityExceedsThreshold => 0x5A
  | .other => 0x4F
  | .quoteNotAvailableForPeggedOrder => 0x42
  | .peggingNotAllowed => 0x50
  | .invalidPrice => 0x58
  | .destinationNotAvailable => 0x47
  | .processingError => 0x4A
  | .invalidRoutingInstructions => 0x4E
  | .invalidDisplayValue => 0x44
  | .outsideOfPermittedTimesForClearingDestination => 0x4D
  | .securityIsHalted => 0x48
  | .invalidSymbol => 0x53
  | .invalidOrderQuantity => 0x51
  | .invalidMinimumQuantity => 0x4B
  | .invalidDestination => 0x57
  | .advanceFeaturesNotAllowed => 0x41
  | .possibleDuplicateOrder => 0x55
  | .invalidOrderType => 0x56
  | .testMode => 0x54
  | .routingNotAllowed => 0x52
  | .orderNotMarketable => 0x46
  | .prmInvalidMessageFormat => 0x61
  | .prmNoQuote => 0x62
  | .prmInvalidAccount => 0x63
  | .prmShortSaleViolation => 0x64
  | .prmIsoOrderCheck => 0x65
  | .prmGtcOrderCheck => 0x66
  | .prmPreMarketOrderCheck => 0x67
  | .prmPostMarketOrderCheck => 0x68
  | .prmDelayedCheckingFlagOff => 0x69
  | .prmExceededMaximumSharesThreshold => 0x6A
  | .prmExceededMaximumValueThreshold => 0x6B
  | .prmRejectAllOrders => 0x6D
  | .prmInvalidPriceFatFinger => 0x6E
  | .prmNotOnEasyToBorrowList => 0x6F
  | .prmNotAvailable => 0x70
  | .prmInvalidMessage => 0x71
  | .prmSnapInProcess => 0x72
  | .prmSymbolHalted => 0x73
  | .prmOnOpen => 0x74
  | .prmOnClose => 0x75
  | .prmProgramTrading => 0x76
  | .prmNotOnRestrictedList => 0x7B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReason :=
  if byte = 0x59 then .noSharesFoundForRouting
  else if byte = 0x43 then .nasdaqOmxPsxIsClosed
  else if byte = 0x49 then .invalidOrderSide
  else if byte = 0x45 then .invalidPeg
  else if byte = 0x4C then .invalidFirm
  else if byte = 0x5A then .quantityExceedsThreshold
  else if byte = 0x4F then .other
  else if byte = 0x42 then .quoteNotAvailableForPeggedOrder
  else if byte = 0x50 then .peggingNotAllowed
  else if byte = 0x58 then .invalidPrice
  else if byte = 0x47 then .destinationNotAvailable
  else if byte = 0x4A then .processingError
  else if byte = 0x4E then .invalidRoutingInstructions
  else if byte = 0x44 then .invalidDisplayValue
  else if byte = 0x4D then .outsideOfPermittedTimesForClearingDestination
  else if byte = 0x48 then .securityIsHalted
  else if byte = 0x53 then .invalidSymbol
  else if byte = 0x51 then .invalidOrderQuantity
  else if byte = 0x4B then .invalidMinimumQuantity
  else if byte = 0x57 then .invalidDestination
  else if byte = 0x41 then .advanceFeaturesNotAllowed
  else if byte = 0x55 then .possibleDuplicateOrder
  else if byte = 0x56 then .invalidOrderType
  else if byte = 0x54 then .testMode
  else if byte = 0x52 then .routingNotAllowed
  else if byte = 0x46 then .orderNotMarketable
  else if byte = 0x61 then .prmInvalidMessageFormat
  else if byte = 0x62 then .prmNoQuote
  else if byte = 0x63 then .prmInvalidAccount
  else if byte = 0x64 then .prmShortSaleViolation
  else if byte = 0x65 then .prmIsoOrderCheck
  else if byte = 0x66 then .prmGtcOrderCheck
  else if byte = 0x67 then .prmPreMarketOrderCheck
  else if byte = 0x68 then .prmPostMarketOrderCheck
  else if byte = 0x69 then .prmDelayedCheckingFlagOff
  else if byte = 0x6A then .prmExceededMaximumSharesThreshold
  else if byte = 0x6B then .prmExceededMaximumValueThreshold
  else if byte = 0x6D then .prmRejectAllOrders
  else if byte = 0x6E then .prmInvalidPriceFatFinger
  else if byte = 0x6F then .prmNotOnEasyToBorrowList
  else if byte = 0x70 then .prmNotAvailable
  else if byte = 0x71 then .prmInvalidMessage
  else if byte = 0x72 then .prmSnapInProcess
  else if byte = 0x73 then .prmSymbolHalted
  else if byte = 0x74 then .prmOnOpen
  else if byte = 0x75 then .prmOnClose
  else if byte = 0x76 then .prmProgramTrading
  else .prmNotOnRestrictedList

def ofByte (byte : UInt8) : RejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReason) : ofByte value.toByte = value := by
  cases value with
  | noSharesFoundForRouting => decide
  | nasdaqOmxPsxIsClosed => decide
  | invalidOrderSide => decide
  | invalidPeg => decide
  | invalidFirm => decide
  | quantityExceedsThreshold => decide
  | other => decide
  | quoteNotAvailableForPeggedOrder => decide
  | peggingNotAllowed => decide
  | invalidPrice => decide
  | destinationNotAvailable => decide
  | processingError => decide
  | invalidRoutingInstructions => decide
  | invalidDisplayValue => decide
  | outsideOfPermittedTimesForClearingDestination => decide
  | securityIsHalted => decide
  | invalidSymbol => decide
  | invalidOrderQuantity => decide
  | invalidMinimumQuantity => decide
  | invalidDestination => decide
  | advanceFeaturesNotAllowed => decide
  | possibleDuplicateOrder => decide
  | invalidOrderType => decide
  | testMode => decide
  | routingNotAllowed => decide
  | orderNotMarketable => decide
  | prmInvalidMessageFormat => decide
  | prmNoQuote => decide
  | prmInvalidAccount => decide
  | prmShortSaleViolation => decide
  | prmIsoOrderCheck => decide
  | prmGtcOrderCheck => decide
  | prmPreMarketOrderCheck => decide
  | prmPostMarketOrderCheck => decide
  | prmDelayedCheckingFlagOff => decide
  | prmExceededMaximumSharesThreshold => decide
  | prmExceededMaximumValueThreshold => decide
  | prmRejectAllOrders => decide
  | prmInvalidPriceFatFinger => decide
  | prmNotOnEasyToBorrowList => decide
  | prmNotAvailable => decide
  | prmInvalidMessage => decide
  | prmSnapInProcess => decide
  | prmSymbolHalted => decide
  | prmOnOpen => decide
  | prmOnClose => decide
  | prmProgramTrading => decide
  | prmNotOnRestrictedList => decide
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
  [0x41, 0x52, 0x4A, 0x58, 0x44, 0x46, 0x47, 0x4F, 0x4D, 0x43, 0x4C, 0x48, 0x4B, 0x59, 0x53, 0x55, 0x42, 0x45, 0x50, 0x54, 0x5A, 0x57, 0x6D, 0x6B, 0x30, 0x37, 0x38, 0x64, 0x65, 0x66, 0x6A, 0x72, 0x74, 0x34, 0x35, 0x36, 0x67]

inductive Liquidity where
  | added -- Added
  | removed -- Removed
  | nonDisplayedAddingLiquidity -- Non Displayed Adding Liquidity
  | routed -- Routed
  | dot -- Dot
  | openingTrade -- Opening Trade
  | onCloseOrder -- On Close Order
  | openingCross -- Opening Cross
  | openingCross_4d -- Opening Cross
  | closingCross -- Closing Cross
  | closingCross_4c -- Closing Cross
  | haltIpoCross -- Halt Ipo Cross
  | haltCross -- Halt Cross
  | reRoutedByNyse -- Re Routed By Nyse
  | oddLotExecution -- Odd Lot Execution
  | addedLiquidity -- Added Liquidity
  | routedToBx -- Routed To Bx
  | nyseOther -- Nyse Other
  | routedToPsx -- Routed To Psx
  | openingTrade_54 -- Opening Trade
  | onCloseOrder_5a -- On Close Order
  | addedPostOnly -- Added Post Only
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | supplementalOrderExecution -- Supplemental Order Execution
  | displayedLiquidityAddingOrderImprovesTheNbbo -- Displayed Liquidity Adding Order Improves The Nbbo
  | displayedLiquidityAddingOrderSetsTheQbboWhileJoiningTheNbbo -- Displayed Liquidity Adding Order Sets The Qbbo While Joining The Nbbo
  | retailDesignatedExecutionThatRemovedLiquidity -- Retail Designated Execution That Removed Liquidity
  | retailDesignatedExecutionThatAddedDisplayedLiquidity -- Retail Designated Execution That Added Displayed Liquidity
  | retailDesignatedExecutionThatAddedNonDisplayedLiquidity -- Retail Designated Execution That Added Non Displayed Liquidity
  | rpiOrderProvidesLiquidity -- Rpi Order Provides Liquidity
  | retailOrderRemovesRpiLiquidity -- Retail Order Removes Rpi Liquidity
  | retailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity -- Retail Order Removes Price Improving Non Displayed Liquidity Other Than Rpi Liquidity
  | addedDisplayedLiquidityInASelectSymbol -- Added Displayed Liquidity In A Select Symbol
  | addedNonDisplayedLiquidityInASelectSymbol -- Added Non Displayed Liquidity In A Select Symbol
  | removedLiquidityInASelectSymbol -- Removed Liquidity In A Select Symbol
  | addedNonDisplayedMidPointLiquidityInASelectSymbol -- Added Non Displayed Mid Point Liquidity In A Select Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ Liquidity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Liquidity

def toByte : Liquidity → UInt8
  | .added => 0x41
  | .removed => 0x52
  | .nonDisplayedAddingLiquidity => 0x4A
  | .routed => 0x58
  | .dot => 0x44
  | .openingTrade => 0x46
  | .onCloseOrder => 0x47
  | .openingCross => 0x4F
  | .openingCross_4d => 0x4D
  | .closingCross => 0x43
  | .closingCross_4c => 0x4C
  | .haltIpoCross => 0x48
  | .haltCross => 0x4B
  | .reRoutedByNyse => 0x59
  | .oddLotExecution => 0x53
  | .addedLiquidity => 0x55
  | .routedToBx => 0x42
  | .nyseOther => 0x45
  | .routedToPsx => 0x50
  | .openingTrade_54 => 0x54
  | .onCloseOrder_5a => 0x5A
  | .addedPostOnly => 0x57
  | .removedLiquidityAtAMidpoint => 0x6D
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .supplementalOrderExecution => 0x30
  | .displayedLiquidityAddingOrderImprovesTheNbbo => 0x37
  | .displayedLiquidityAddingOrderSetsTheQbboWhileJoiningTheNbbo => 0x38
  | .retailDesignatedExecutionThatRemovedLiquidity => 0x64
  | .retailDesignatedExecutionThatAddedDisplayedLiquidity => 0x65
  | .retailDesignatedExecutionThatAddedNonDisplayedLiquidity => 0x66
  | .rpiOrderProvidesLiquidity => 0x6A
  | .retailOrderRemovesRpiLiquidity => 0x72
  | .retailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity => 0x74
  | .addedDisplayedLiquidityInASelectSymbol => 0x34
  | .addedNonDisplayedLiquidityInASelectSymbol => 0x35
  | .removedLiquidityInASelectSymbol => 0x36
  | .addedNonDisplayedMidPointLiquidityInASelectSymbol => 0x67
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Liquidity :=
  if byte = 0x41 then .added
  else if byte = 0x52 then .removed
  else if byte = 0x4A then .nonDisplayedAddingLiquidity
  else if byte = 0x58 then .routed
  else if byte = 0x44 then .dot
  else if byte = 0x46 then .openingTrade
  else if byte = 0x47 then .onCloseOrder
  else if byte = 0x4F then .openingCross
  else if byte = 0x4D then .openingCross_4d
  else if byte = 0x43 then .closingCross
  else if byte = 0x4C then .closingCross_4c
  else if byte = 0x48 then .haltIpoCross
  else if byte = 0x4B then .haltCross
  else if byte = 0x59 then .reRoutedByNyse
  else if byte = 0x53 then .oddLotExecution
  else if byte = 0x55 then .addedLiquidity
  else if byte = 0x42 then .routedToBx
  else if byte = 0x45 then .nyseOther
  else if byte = 0x50 then .routedToPsx
  else if byte = 0x54 then .openingTrade_54
  else if byte = 0x5A then .onCloseOrder_5a
  else if byte = 0x57 then .addedPostOnly
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else if byte = 0x6B then .addedLiquidityViaAMidpointOrder
  else if byte = 0x30 then .supplementalOrderExecution
  else if byte = 0x37 then .displayedLiquidityAddingOrderImprovesTheNbbo
  else if byte = 0x38 then .displayedLiquidityAddingOrderSetsTheQbboWhileJoiningTheNbbo
  else if byte = 0x64 then .retailDesignatedExecutionThatRemovedLiquidity
  else if byte = 0x65 then .retailDesignatedExecutionThatAddedDisplayedLiquidity
  else if byte = 0x66 then .retailDesignatedExecutionThatAddedNonDisplayedLiquidity
  else if byte = 0x6A then .rpiOrderProvidesLiquidity
  else if byte = 0x72 then .retailOrderRemovesRpiLiquidity
  else if byte = 0x74 then .retailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity
  else if byte = 0x34 then .addedDisplayedLiquidityInASelectSymbol
  else if byte = 0x35 then .addedNonDisplayedLiquidityInASelectSymbol
  else if byte = 0x36 then .removedLiquidityInASelectSymbol
  else .addedNonDisplayedMidPointLiquidityInASelectSymbol

def ofByte (byte : UInt8) : Liquidity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Liquidity) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | removed => decide
  | nonDisplayedAddingLiquidity => decide
  | routed => decide
  | dot => decide
  | openingTrade => decide
  | onCloseOrder => decide
  | openingCross => decide
  | openingCross_4d => decide
  | closingCross => decide
  | closingCross_4c => decide
  | haltIpoCross => decide
  | haltCross => decide
  | reRoutedByNyse => decide
  | oddLotExecution => decide
  | addedLiquidity => decide
  | routedToBx => decide
  | nyseOther => decide
  | routedToPsx => decide
  | openingTrade_54 => decide
  | onCloseOrder_5a => decide
  | addedPostOnly => decide
  | removedLiquidityAtAMidpoint => decide
  | addedLiquidityViaAMidpointOrder => decide
  | supplementalOrderExecution => decide
  | displayedLiquidityAddingOrderImprovesTheNbbo => decide
  | displayedLiquidityAddingOrderSetsTheQbboWhileJoiningTheNbbo => decide
  | retailDesignatedExecutionThatRemovedLiquidity => decide
  | retailDesignatedExecutionThatAddedDisplayedLiquidity => decide
  | retailDesignatedExecutionThatAddedNonDisplayedLiquidity => decide
  | rpiOrderProvidesLiquidity => decide
  | retailOrderRemovesRpiLiquidity => decide
  | retailOrderRemovesPriceImprovingNonDisplayedLiquidityOtherThanRpiLiquidity => decide
  | addedDisplayedLiquidityInASelectSymbol => decide
  | addedNonDisplayedLiquidityInASelectSymbol => decide
  | removedLiquidityInASelectSymbol => decide
  | addedNonDisplayedMidPointLiquidityInASelectSymbol => decide
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

/-- Reference Price Type: one byte code -/
def ReferencePriceType.codes : List UInt8 :=
  [0x49]

inductive ReferencePriceType where
  | intradayIndicativeValue -- Intraday Indicative Value
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceType

def toByte : ReferencePriceType → UInt8
  | .intradayIndicativeValue => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ReferencePriceType :=
  .intradayIndicativeValue

def ofByte (byte : UInt8) : ReferencePriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceType) : ofByte value.toByte = value := by
  cases value with
  | intradayIndicativeValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceType

/-- Trade Correction Reason: one byte code -/
def TradeCorrectionReason.codes : List UInt8 :=
  [0x4E]

inductive TradeCorrectionReason where
  | adjustedToNav -- Adjusted To Nav
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCorrectionReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCorrectionReason

def toByte : TradeCorrectionReason → UInt8
  | .adjustedToNav => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TradeCorrectionReason :=
  .adjustedToNav

def ofByte (byte : UInt8) : TradeCorrectionReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCorrectionReason) : ofByte value.toByte = value := by
  cases value with
  | adjustedToNav => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCorrectionReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCorrectionReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCorrectionReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCorrectionReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCorrectionReason

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

/-- Executed With Reference Price Message: 51 bytes -/
structure ExecutedWithReferencePriceMessage where
  orderTokenClientOrderId : Alpha 14
  shares : Alpha 6
  price : Alpha 10
  liquidity : Liquidity
  matchNumber : Alpha 9
  referencePrice : Alpha 10
  referencePriceType : ReferencePriceType
  deriving DecidableEq, Repr

namespace ExecutedWithReferencePriceMessage

def encode (message : ExecutedWithReferencePriceMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.price
    ++ (Liquidity.encode message.liquidity
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.referencePrice
    ++ (ReferencePriceType.encode message.referencePriceType))))))

def decode (bytes : List UInt8) : Option (ExecutedWithReferencePriceMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (liquidity, bytes) ← Liquidity.decode bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (referencePrice, bytes) ← Alpha.decode 10 bytes
  let (referencePriceType, bytes) ← ReferencePriceType.decode bytes
  pure ({ orderTokenClientOrderId, shares, price, liquidity, matchNumber, referencePrice, referencePriceType }, bytes)

@[simp] theorem encode_length (message : ExecutedWithReferencePriceMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Liquidity.encode_length, ReferencePriceType.encode_length]

theorem encode_length_pos (message : ExecutedWithReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedWithReferencePriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceType.decode_encode, some_bind]
  rfl

end ExecutedWithReferencePriceMessage

/-- Trade Correction Message: 41 bytes -/
structure TradeCorrectionMessage where
  orderTokenClientOrderId : Alpha 14
  shares : Alpha 6
  price : Alpha 10
  liquidity : Liquidity
  matchNumber : Alpha 9
  tradeCorrectionReason : TradeCorrectionReason
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.price
    ++ (Liquidity.encode message.liquidity
    ++ (Alpha.encode message.matchNumber
    ++ (TradeCorrectionReason.encode message.tradeCorrectionReason)))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (liquidity, bytes) ← Liquidity.decode bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (tradeCorrectionReason, bytes) ← TradeCorrectionReason.decode bytes
  pure ({ orderTokenClientOrderId, shares, price, liquidity, matchNumber, tradeCorrectionReason }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Liquidity.encode_length, TradeCorrectionReason.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TradeCorrectionReason.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | acceptedOrderMessage (message : AcceptedOrderMessage) -- "A" 0x41
  | acceptedOrderMessageWithCrossFunctionality (message : AcceptedOrderMessageWithCrossFunctionality) -- "R" 0x52
  | canceledOrderMessage (message : CanceledOrderMessage) -- "C" 0x43
  | rejectedOrderMessage (message : RejectedOrderMessage) -- "J" 0x4A
  | executedOrderMessage (message : ExecutedOrderMessage) -- "E" 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | executedWithReferencePriceMessage (message : ExecutedWithReferencePriceMessage) -- "G" 0x47
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "F" 0x46
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
  | .executedWithReferencePriceMessage _ => 71
  | .tradeCorrectionMessage _ => 70

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .acceptedOrderMessage message => AcceptedOrderMessage.encode message
  | .acceptedOrderMessageWithCrossFunctionality message => AcceptedOrderMessageWithCrossFunctionality.encode message
  | .canceledOrderMessage message => CanceledOrderMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .executedOrderMessage message => ExecutedOrderMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .executedWithReferencePriceMessage message => ExecutedWithReferencePriceMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message

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
  | executedWithReferencePriceMessage inner =>
    simp only [encode, ExecutedWithReferencePriceMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AcceptedOrderMessage.decode bytes).map fun (message, rest) => (.acceptedOrderMessage message, rest)
  else if tag = 82 then (AcceptedOrderMessageWithCrossFunctionality.decode bytes).map fun (message, rest) => (.acceptedOrderMessageWithCrossFunctionality message, rest)
  else if tag = 67 then (CanceledOrderMessage.decode bytes).map fun (message, rest) => (.canceledOrderMessage message, rest)
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun (message, rest) => (.rejectedOrderMessage message, rest)
  else if tag = 69 then (ExecutedOrderMessage.decode bytes).map fun (message, rest) => (.executedOrderMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 71 then (ExecutedWithReferencePriceMessage.decode bytes).map fun (message, rest) => (.executedWithReferencePriceMessage message, rest)
  else if tag = 70 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
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
  | executedWithReferencePriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ExecutedWithReferencePriceMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeCorrectionMessage.encode_length]
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

end Omi.NasdaqNsmequitiesRashAsciirashV112016Server
