import Omi.Wire

/-!
# Box Options Market Sola Multicast v1.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Levels counts Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Levels counts Complex Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Legs counts Instrument Leg in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BoxBoxoptionsSolamulticastHsvfV18

/-- Expiry Month Code: one byte code -/
def ExpiryMonthCode.codes : List UInt8 :=
  [0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive ExpiryMonthCode where
  | januaryPut -- January Put
  | februaryPut -- February Put
  | marchPut -- March Put
  | aprilPut -- April Put
  | mayPut -- May Put
  | junePut -- June Put
  | julyPut -- July Put
  | augustPut -- August Put
  | septemberPut -- September Put
  | octoberPut -- October Put
  | novemberPut -- November Put
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryMonthCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryMonthCode

def toByte : ExpiryMonthCode → UInt8
  | .januaryPut => 0x4D
  | .februaryPut => 0x4E
  | .marchPut => 0x4F
  | .aprilPut => 0x50
  | .mayPut => 0x51
  | .junePut => 0x52
  | .julyPut => 0x53
  | .augustPut => 0x54
  | .septemberPut => 0x55
  | .octoberPut => 0x56
  | .novemberPut => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpiryMonthCode :=
  if byte = 0x4D then .januaryPut
  else if byte = 0x4E then .februaryPut
  else if byte = 0x4F then .marchPut
  else if byte = 0x50 then .aprilPut
  else if byte = 0x51 then .mayPut
  else if byte = 0x52 then .junePut
  else if byte = 0x53 then .julyPut
  else if byte = 0x54 then .augustPut
  else if byte = 0x55 then .septemberPut
  else if byte = 0x56 then .octoberPut
  else .novemberPut

def ofByte (byte : UInt8) : ExpiryMonthCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryMonthCode) : ofByte value.toByte = value := by
  cases value with
  | januaryPut => decide
  | februaryPut => decide
  | marchPut => decide
  | aprilPut => decide
  | mayPut => decide
  | junePut => decide
  | julyPut => decide
  | augustPut => decide
  | septemberPut => decide
  | octoberPut => decide
  | novemberPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryMonthCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryMonthCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryMonthCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExpiryMonthCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryMonthCode

/-- Net Change Sign: one byte code -/
def NetChangeSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive NetChangeSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ NetChangeSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetChangeSign

def toByte : NetChangeSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetChangeSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : NetChangeSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetChangeSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetChangeSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetChangeSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetChangeSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NetChangeSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetChangeSign

/-- Price Indicator Marker: one byte code -/
def PriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x43, 0x4C, 0x4F, 0x53, 0x57, 0x58, 0x47, 0x49, 0x50, 0x20]

inductive PriceIndicatorMarker where
  | asOfTrade -- As Of Trade
  | tradesPerformedAtTheEndOfAPipAllocationPhase -- Trades Performed At The End Of A Pip Allocation Phase
  | lateTrade -- Late Trade
  | tradesPerformedDuringTheOpening -- Trades Performed During The Opening
  | referencePrice -- Reference Price
  | tradesResultingFromTheTransmissionOfAnIsoInboundOrder -- Trades Resulting From The Transmission Of An Iso Inbound Order
  | tradesPerformedWhenTheMarketIsCrossed -- Trades Performed When The Market Is Crossed
  | contingentTradePriceOfTheTradeWasNotControlledAgainstTheNbbo -- Contingent Trade Price Of The Trade Was Not Controlled Against The Nbbo
  | tradeInvolvingAnImpliedOrderOrLegTradeOfAComplexOrderInstrument -- Trade Involving An Implied Order Or Leg Trade Of A Complex Order Instrument
  | tradeDoneOnAComplexOrderInstrument -- Trade Done On A Complex Order Instrument
  | actualTransactionTookPlace -- Actual Transaction Took Place
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceIndicatorMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceIndicatorMarker

def toByte : PriceIndicatorMarker → UInt8
  | .asOfTrade => 0x41
  | .tradesPerformedAtTheEndOfAPipAllocationPhase => 0x43
  | .lateTrade => 0x4C
  | .tradesPerformedDuringTheOpening => 0x4F
  | .referencePrice => 0x53
  | .tradesResultingFromTheTransmissionOfAnIsoInboundOrder => 0x57
  | .tradesPerformedWhenTheMarketIsCrossed => 0x58
  | .contingentTradePriceOfTheTradeWasNotControlledAgainstTheNbbo => 0x47
  | .tradeInvolvingAnImpliedOrderOrLegTradeOfAComplexOrderInstrument => 0x49
  | .tradeDoneOnAComplexOrderInstrument => 0x50
  | .actualTransactionTookPlace => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceIndicatorMarker :=
  if byte = 0x41 then .asOfTrade
  else if byte = 0x43 then .tradesPerformedAtTheEndOfAPipAllocationPhase
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4F then .tradesPerformedDuringTheOpening
  else if byte = 0x53 then .referencePrice
  else if byte = 0x57 then .tradesResultingFromTheTransmissionOfAnIsoInboundOrder
  else if byte = 0x58 then .tradesPerformedWhenTheMarketIsCrossed
  else if byte = 0x47 then .contingentTradePriceOfTheTradeWasNotControlledAgainstTheNbbo
  else if byte = 0x49 then .tradeInvolvingAnImpliedOrderOrLegTradeOfAComplexOrderInstrument
  else if byte = 0x50 then .tradeDoneOnAComplexOrderInstrument
  else .actualTransactionTookPlace

def ofByte (byte : UInt8) : PriceIndicatorMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceIndicatorMarker) : ofByte value.toByte = value := by
  cases value with
  | asOfTrade => decide
  | tradesPerformedAtTheEndOfAPipAllocationPhase => decide
  | lateTrade => decide
  | tradesPerformedDuringTheOpening => decide
  | referencePrice => decide
  | tradesResultingFromTheTransmissionOfAnIsoInboundOrder => decide
  | tradesPerformedWhenTheMarketIsCrossed => decide
  | contingentTradePriceOfTheTradeWasNotControlledAgainstTheNbbo => decide
  | tradeInvolvingAnImpliedOrderOrLegTradeOfAComplexOrderInstrument => decide
  | tradeDoneOnAComplexOrderInstrument => decide
  | actualTransactionTookPlace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceIndicatorMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceIndicatorMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceIndicatorMarker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceIndicatorMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceIndicatorMarker

/-- Instrument Status Marker: one byte code -/
def InstrumentStatusMarker.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x48, 0x52, 0x53, 0x5A, 0x41, 0x43, 0x42]

inductive InstrumentStatusMarker where
  | preopeningPhase -- Preopening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | tradingHalted -- Trading Halted
  | reservedPhase -- Reserved Phase
  | suspendedPhase -- Suspended Phase
  | frozen -- Frozen
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | closed -- Closed
  | beginningOfDayInquiries -- Beginning Of Day Inquiries
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatusMarker

def toByte : InstrumentStatusMarker → UInt8
  | .preopeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .tradingHalted => 0x48
  | .reservedPhase => 0x52
  | .suspendedPhase => 0x53
  | .frozen => 0x5A
  | .surveillanceInterventionPhase => 0x41
  | .closed => 0x43
  | .beginningOfDayInquiries => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatusMarker :=
  if byte = 0x59 then .preopeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x52 then .reservedPhase
  else if byte = 0x53 then .suspendedPhase
  else if byte = 0x5A then .frozen
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .closed
  else .beginningOfDayInquiries

def ofByte (byte : UInt8) : InstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preopeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | tradingHalted => decide
  | reservedPhase => decide
  | suspendedPhase => decide
  | frozen => decide
  | surveillanceInterventionPhase => decide
  | closed => decide
  | beginningOfDayInquiries => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatusMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatusMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatusMarker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentStatusMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatusMarker

/-- Ask Price Sign: one byte code -/
def AskPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive AskPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ AskPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskPriceSign

def toByte : AskPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : AskPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AskPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskPriceSign

/-- Group Status: one byte code -/
def GroupStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x48, 0x41, 0x43, 0x42]

inductive GroupStatus where
  | preopeningPhase -- Preopening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | tradingHalted -- Trading Halted
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | closed -- Closed
  | beginningOfDayInquiries -- Beginning Of Day Inquiries
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupStatus

def toByte : GroupStatus → UInt8
  | .preopeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .tradingHalted => 0x48
  | .surveillanceInterventionPhase => 0x41
  | .closed => 0x43
  | .beginningOfDayInquiries => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupStatus :=
  if byte = 0x59 then .preopeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .closed
  else .beginningOfDayInquiries

def ofByte (byte : UInt8) : GroupStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupStatus) : ofByte value.toByte = value := by
  cases value with
  | preopeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | tradingHalted => decide
  | surveillanceInterventionPhase => decide
  | closed => decide
  | beginningOfDayInquiries => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GroupStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GroupStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GroupStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : GroupStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GroupStatus

/-- Level Of Market Depth: one byte code -/
def LevelOfMarketDepth.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x41, 0x50]

inductive LevelOfMarketDepth where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | level4 -- Level 4
  | level5 -- Level 5
  | level6 -- Level 6
  | impliedPrice -- Implied Price
  | publicCustomerVolume -- Public Customer Volume
  | unlisted (byte : { byte : UInt8 // byte ∉ LevelOfMarketDepth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LevelOfMarketDepth

def toByte : LevelOfMarketDepth → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .level4 => 0x34
  | .level5 => 0x35
  | .level6 => 0x36
  | .impliedPrice => 0x41
  | .publicCustomerVolume => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LevelOfMarketDepth :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else if byte = 0x33 then .level3
  else if byte = 0x34 then .level4
  else if byte = 0x35 then .level5
  else if byte = 0x36 then .level6
  else if byte = 0x41 then .impliedPrice
  else .publicCustomerVolume

def ofByte (byte : UInt8) : LevelOfMarketDepth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LevelOfMarketDepth) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | level4 => decide
  | level5 => decide
  | level6 => decide
  | impliedPrice => decide
  | publicCustomerVolume => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LevelOfMarketDepth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LevelOfMarketDepth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LevelOfMarketDepth) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LevelOfMarketDepth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LevelOfMarketDepth

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x41, 0x45]

inductive OptionType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Type Of Instrument: one byte code -/
def TypeOfInstrument.codes : List UInt8 :=
  [0x4F, 0x4C]

inductive TypeOfInstrument where
  | options -- Options
  | longTerm -- Long Term
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfInstrument.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfInstrument

def toByte : TypeOfInstrument → UInt8
  | .options => 0x4F
  | .longTerm => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfInstrument :=
  if byte = 0x4F then .options
  else .longTerm

def ofByte (byte : UInt8) : TypeOfInstrument :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfInstrument) : ofByte value.toByte = value := by
  cases value with
  | options => decide
  | longTerm => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfInstrument) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfInstrument × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfInstrument) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfInstrument) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfInstrument

/-- Type Of Underlying: one byte code -/
def TypeOfUnderlying.codes : List UInt8 :=
  [0x58, 0x45]

inductive TypeOfUnderlying where
  | index -- Index
  | equities -- Equities
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfUnderlying.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfUnderlying

def toByte : TypeOfUnderlying → UInt8
  | .index => 0x58
  | .equities => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfUnderlying :=
  if byte = 0x58 then .index
  else .equities

def ofByte (byte : UInt8) : TypeOfUnderlying :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfUnderlying) : ofByte value.toByte = value := by
  cases value with
  | index => decide
  | equities => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfUnderlying) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfUnderlying × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfUnderlying) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfUnderlying) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfUnderlying

/-- Type Of Options: one byte code -/
def TypeOfOptions.codes : List UInt8 :=
  [0x20]

inductive TypeOfOptions where
  | regular -- Regular
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfOptions.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfOptions

def toByte : TypeOfOptions → UInt8
  | .regular => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TypeOfOptions :=
  .regular

def ofByte (byte : UInt8) : TypeOfOptions :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfOptions) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfOptions) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfOptions × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfOptions) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfOptions) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfOptions

/-- Delivery Month: one byte code -/
def DeliveryMonth.codes : List UInt8 :=
  [0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive DeliveryMonth where
  | januaryPut -- January Put
  | februaryPut -- February Put
  | marchPut -- March Put
  | aprilPut -- April Put
  | mayPut -- May Put
  | junePut -- June Put
  | julyPut -- July Put
  | augustPut -- August Put
  | septemberPut -- September Put
  | octoberPut -- October Put
  | novemberPut -- November Put
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryMonth

def toByte : DeliveryMonth → UInt8
  | .januaryPut => 0x4D
  | .februaryPut => 0x4E
  | .marchPut => 0x4F
  | .aprilPut => 0x50
  | .mayPut => 0x51
  | .junePut => 0x52
  | .julyPut => 0x53
  | .augustPut => 0x54
  | .septemberPut => 0x55
  | .octoberPut => 0x56
  | .novemberPut => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryMonth :=
  if byte = 0x4D then .januaryPut
  else if byte = 0x4E then .februaryPut
  else if byte = 0x4F then .marchPut
  else if byte = 0x50 then .aprilPut
  else if byte = 0x51 then .mayPut
  else if byte = 0x52 then .junePut
  else if byte = 0x53 then .julyPut
  else if byte = 0x54 then .augustPut
  else if byte = 0x55 then .septemberPut
  else if byte = 0x56 then .octoberPut
  else .novemberPut

def ofByte (byte : UInt8) : DeliveryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryMonth) : ofByte value.toByte = value := by
  cases value with
  | januaryPut => decide
  | februaryPut => decide
  | marchPut => decide
  | aprilPut => decide
  | mayPut => decide
  | junePut => decide
  | julyPut => decide
  | augustPut => decide
  | septemberPut => decide
  | octoberPut => decide
  | novemberPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryMonth) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeliveryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryMonth

/-- Max Threshold Price Sign: one byte code -/
def MaxThresholdPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive MaxThresholdPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ MaxThresholdPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MaxThresholdPriceSign

def toByte : MaxThresholdPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MaxThresholdPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : MaxThresholdPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MaxThresholdPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MaxThresholdPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MaxThresholdPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MaxThresholdPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MaxThresholdPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MaxThresholdPriceSign

/-- Min Threshold Price Sign: one byte code -/
def MinThresholdPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive MinThresholdPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ MinThresholdPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MinThresholdPriceSign

def toByte : MinThresholdPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MinThresholdPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : MinThresholdPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MinThresholdPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MinThresholdPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MinThresholdPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MinThresholdPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MinThresholdPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MinThresholdPriceSign

/-- Complex Order Instrument Allow Implied: one byte code -/
def ComplexOrderInstrumentAllowImplied.codes : List UInt8 :=
  [0x4E, 0x43, 0x53]

inductive ComplexOrderInstrumentAllowImplied where
  | no -- No
  | continuousImplied -- Continuous Implied
  | snapshotImplied -- Snapshot Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplexOrderInstrumentAllowImplied.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplexOrderInstrumentAllowImplied

def toByte : ComplexOrderInstrumentAllowImplied → UInt8
  | .no => 0x4E
  | .continuousImplied => 0x43
  | .snapshotImplied => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplexOrderInstrumentAllowImplied :=
  if byte = 0x4E then .no
  else if byte = 0x43 then .continuousImplied
  else .snapshotImplied

def ofByte (byte : UInt8) : ComplexOrderInstrumentAllowImplied :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplexOrderInstrumentAllowImplied) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | continuousImplied => decide
  | snapshotImplied => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplexOrderInstrumentAllowImplied) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplexOrderInstrumentAllowImplied × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplexOrderInstrumentAllowImplied) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ComplexOrderInstrumentAllowImplied) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplexOrderInstrumentAllowImplied

/-- Leg Ratio Sign: one byte code -/
def LegRatioSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LegRatioSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LegRatioSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegRatioSign

def toByte : LegRatioSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegRatioSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LegRatioSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegRatioSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegRatioSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegRatioSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegRatioSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegRatioSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegRatioSign

/-- Bulletin Type: one byte code -/
def BulletinType.codes : List UInt8 :=
  [0x31, 0x32]

inductive BulletinType where
  | regular -- Regular
  | special -- Special
  | unlisted (byte : { byte : UInt8 // byte ∉ BulletinType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BulletinType

def toByte : BulletinType → UInt8
  | .regular => 0x31
  | .special => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BulletinType :=
  if byte = 0x31 then .regular
  else .special

def ofByte (byte : UInt8) : BulletinType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BulletinType) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | special => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BulletinType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BulletinType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BulletinType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BulletinType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BulletinType

/-- Continue Marker: one byte code -/
def ContinueMarker.codes : List UInt8 :=
  [0x30, 0x31]

inductive ContinueMarker where
  | bulletinContinuesInNextRecord -- Bulletin Continues In Next Record
  | bulletinEnded -- Bulletin Ended
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinueMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinueMarker

def toByte : ContinueMarker → UInt8
  | .bulletinContinuesInNextRecord => 0x30
  | .bulletinEnded => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContinueMarker :=
  if byte = 0x30 then .bulletinContinuesInNextRecord
  else .bulletinEnded

def ofByte (byte : UInt8) : ContinueMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinueMarker) : ofByte value.toByte = value := by
  cases value with
  | bulletinContinuesInNextRecord => decide
  | bulletinEnded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinueMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinueMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinueMarker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContinueMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinueMarker

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive Tick where
  | uptick -- Uptick
  | downtick -- Downtick
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .uptick => 0x2B
  | .downtick => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x2B then .uptick
  else .downtick

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | uptick => decide
  | downtick => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tick) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tick × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tick) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tick) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tick

/-- Open Price Sign: one byte code -/
def OpenPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive OpenPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenPriceSign

def toByte : OpenPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : OpenPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenPriceSign

/-- High Price Sign: one byte code -/
def HighPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive HighPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ HighPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HighPriceSign

def toByte : HighPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HighPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : HighPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HighPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HighPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HighPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HighPriceSign

/-- Low Price Sign: one byte code -/
def LowPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LowPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LowPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LowPriceSign

def toByte : LowPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LowPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LowPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LowPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LowPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LowPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LowPriceSign

/-- Initial Order Side: one byte code -/
def InitialOrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive InitialOrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ InitialOrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitialOrderSide

def toByte : InitialOrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitialOrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : InitialOrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitialOrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitialOrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitialOrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitialOrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InitialOrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitialOrderSide

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x47, 0x42, 0x43, 0x46]

inductive AuctionType where
  | regularPip -- Regular Pip
  | solicitation -- Solicitation
  | facilitation -- Facilitation
  | exposedOrder -- Exposed Order
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .regularPip => 0x47
  | .solicitation => 0x42
  | .facilitation => 0x43
  | .exposedOrder => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x47 then .regularPip
  else if byte = 0x42 then .solicitation
  else if byte = 0x43 then .facilitation
  else .exposedOrder

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | regularPip => decide
  | solicitation => decide
  | facilitation => decide
  | exposedOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Initial Order Price Sign: one byte code -/
def InitialOrderPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive InitialOrderPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ InitialOrderPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitialOrderPriceSign

def toByte : InitialOrderPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitialOrderPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : InitialOrderPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitialOrderPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitialOrderPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitialOrderPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitialOrderPriceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InitialOrderPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitialOrderPriceSign

/-- Order Side: one byte code -/
def OrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSide

def toByte : OrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSide

/-- Type Of Order: one byte code -/
def TypeOfOrder.codes : List UInt8 :=
  [0x41, 0x50]

inductive TypeOfOrder where
  | initialOrder -- Initial Order
  | exposedOrder -- Exposed Order
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfOrder.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfOrder

def toByte : TypeOfOrder → UInt8
  | .initialOrder => 0x41
  | .exposedOrder => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfOrder :=
  if byte = 0x41 then .initialOrder
  else .exposedOrder

def ofByte (byte : UInt8) : TypeOfOrder :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfOrder) : ofByte value.toByte = value := by
  cases value with
  | initialOrder => decide
  | exposedOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfOrder) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfOrder × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfOrder) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfOrder) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfOrder

/-- Type Of Clearing Account: one byte code -/
def TypeOfClearingAccount.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x57, 0x58]

inductive TypeOfClearingAccount where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfClearingAccount.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfClearingAccount

def toByte : TypeOfClearingAccount → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfClearingAccount :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else .awayMarketMaker

def ofByte (byte : UInt8) : TypeOfClearingAccount :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfClearingAccount) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfClearingAccount) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfClearingAccount × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfClearingAccount) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfClearingAccount) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfClearingAccount

/-- Limit Entered For An Order Sign: one byte code -/
def LimitEnteredForAnOrderSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LimitEnteredForAnOrderSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitEnteredForAnOrderSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitEnteredForAnOrderSign

def toByte : LimitEnteredForAnOrderSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitEnteredForAnOrderSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LimitEnteredForAnOrderSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitEnteredForAnOrderSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitEnteredForAnOrderSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitEnteredForAnOrderSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitEnteredForAnOrderSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LimitEnteredForAnOrderSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitEnteredForAnOrderSign

/-- Deletion Type: one byte code -/
def DeletionType.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive DeletionType where
  | preciseOrder -- Precise Order
  | allPreviousOrdersInTheSpecifiedSide -- All Previous Orders In The Specified Side
  | allOrders -- All Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ DeletionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeletionType

def toByte : DeletionType → UInt8
  | .preciseOrder => 0x31
  | .allPreviousOrdersInTheSpecifiedSide => 0x32
  | .allOrders => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeletionType :=
  if byte = 0x31 then .preciseOrder
  else if byte = 0x32 then .allPreviousOrdersInTheSpecifiedSide
  else .allOrders

def ofByte (byte : UInt8) : DeletionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeletionType) : ofByte value.toByte = value := by
  cases value with
  | preciseOrder => decide
  | allPreviousOrdersInTheSpecifiedSide => decide
  | allOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeletionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeletionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeletionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeletionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeletionType

/-- Improvement Order Side: one byte code -/
def ImprovementOrderSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImprovementOrderSide where
  | buy -- Buy
  | sell -- Sell
  | all -- All
  | unlisted (byte : { byte : UInt8 // byte ∉ ImprovementOrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImprovementOrderSide

def toByte : ImprovementOrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .all => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImprovementOrderSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .all

def ofByte (byte : UInt8) : ImprovementOrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImprovementOrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | all => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImprovementOrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImprovementOrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImprovementOrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImprovementOrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImprovementOrderSide

/-- End Of Transmission Message: 7 bytes -/
structure EndOfTransmissionMessage where
  exchangeId : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 6 bytes -/
structure CircuitAssuranceMessage where
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  Alpha.encode message.time

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- System Timestamp Message: 9 bytes -/
structure SystemTimestampMessage where
  tradingEngineTimestamp : Alpha 9
  deriving DecidableEq, Repr

namespace SystemTimestampMessage

def encode (message : SystemTimestampMessage) : List UInt8 :=
  Alpha.encode message.tradingEngineTimestamp

def decode (bytes : List UInt8) : Option (SystemTimestampMessage × List UInt8) := do
  let (tradingEngineTimestamp, bytes) ← Alpha.decode 9 bytes
  pure ({ tradingEngineTimestamp }, bytes)

@[simp] theorem encode_length (message : SystemTimestampMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SystemTimestampMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemTimestampMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemTimestampMessage

/-- Instrument Description: 20 bytes -/
structure InstrumentDescription where
  rootSymbol : Alpha 6
  expiryMonthCode : ExpiryMonthCode
  filler1 : Alpha 1
  strikePrice : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace InstrumentDescription

def encode (message : InstrumentDescription) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (ExpiryMonthCode.encode message.expiryMonthCode
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay))))))

def decode (bytes : List UInt8) : Option (InstrumentDescription × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthCode, bytes) ← ExpiryMonthCode.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, expiryMonthCode, filler1, strikePrice, strikePriceFractionIndicator, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : InstrumentDescription) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonthCode.encode_length]

theorem encode_length_pos (message : InstrumentDescription) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDescription) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthCode.decode_encode, some_bind]
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

end InstrumentDescription

/-- Option Trade Message: 65 bytes -/
structure OptionTradeMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : NetChangeSign
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 6
  openInterest : Alpha 7
  filler1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  pure ({ exchangeId, instrumentDescription, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, openInterest, filler1, priceIndicatorMarker }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, NetChangeSign.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PriceIndicatorMarker.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Complex Order Instrument Trade Message: 68 bytes -/
structure ComplexOrderInstrumentTradeMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : NetChangeSign
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 6
  priceIndicatorMarker : PriceIndicatorMarker
  deriving DecidableEq, Repr

namespace ComplexOrderInstrumentTradeMessage

def encode (message : ComplexOrderInstrumentTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker)))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderInstrumentTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, priceIndicatorMarker }, bytes)

@[simp] theorem encode_length (message : ComplexOrderInstrumentTradeMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NetChangeSign.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : ComplexOrderInstrumentTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderInstrumentTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PriceIndicatorMarker.decode_encode, some_bind]
  rfl

end ComplexOrderInstrumentTradeMessage

/-- Option Request For Quote Message: 29 bytes -/
structure OptionRequestForQuoteMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  requestedSize : Alpha 8
  deriving DecidableEq, Repr

namespace OptionRequestForQuoteMessage

def encode (message : OptionRequestForQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.requestedSize))

def decode (bytes : List UInt8) : Option (OptionRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, instrumentDescription, requestedSize }, bytes)

@[simp] theorem encode_length (message : OptionRequestForQuoteMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length]

theorem encode_length_pos (message : OptionRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionRequestForQuoteMessage

/-- Option Quote Message: 57 bytes -/
structure OptionQuoteMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  filler1 : Alpha 1
  instrumentStatusMarker : InstrumentStatusMarker
  publicCustomerBidSize : Alpha 5
  publicCustomerAskSize : Alpha 5
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.filler1
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.publicCustomerBidSize
    ++ (Alpha.encode message.publicCustomerAskSize)))))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (publicCustomerBidSize, bytes) ← Alpha.decode 5 bytes
  let (publicCustomerAskSize, bytes) ← Alpha.decode 5 bytes
  pure ({ exchangeId, instrumentDescription, bidPrice, bidPriceFractionIndicator, bidSize, askPrice, askPriceFractionIndicator, askSize, filler1, instrumentStatusMarker, publicCustomerBidSize, publicCustomerAskSize }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Complex Order Quote Message: 68 bytes -/
structure ComplexOrderQuoteMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  publicCustomerBidSize : Alpha 5
  publicCustomerAskSize : Alpha 5
  deriving DecidableEq, Repr

namespace ComplexOrderQuoteMessage

def encode (message : ComplexOrderQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.publicCustomerBidSize
    ++ (Alpha.encode message.publicCustomerAskSize))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (publicCustomerBidSize, bytes) ← Alpha.decode 5 bytes
  let (publicCustomerAskSize, bytes) ← Alpha.decode 5 bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, bidPriceSign, bidPrice, bidPriceFractionIndicator, bidSize, askPriceSign, askPrice, askPriceFractionIndicator, askSize, instrumentStatusMarker, publicCustomerBidSize, publicCustomerAskSize }, bytes)

@[simp] theorem encode_length (message : ComplexOrderQuoteMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskPriceSign.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : ComplexOrderQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexOrderQuoteMessage

/-- Group Opening Time Message: 14 bytes -/
structure GroupOpeningTimeMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  groupStatus : GroupStatus
  scheduledTime : Alpha 6
  deriving DecidableEq, Repr

namespace GroupOpeningTimeMessage

def encode (message : GroupOpeningTimeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (GroupStatus.encode message.groupStatus
    ++ (Alpha.encode message.scheduledTime)))

def decode (bytes : List UInt8) : Option (GroupOpeningTimeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  let (scheduledTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, groupStatus, scheduledTime }, bytes)

@[simp] theorem encode_length (message : GroupOpeningTimeMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupOpeningTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupOpeningTimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, GroupStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupOpeningTimeMessage

/-- Group Status Message: 8 bytes -/
structure GroupStatusMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (GroupStatus.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ exchangeId, rootSymbol, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Strategies Group Status Message: 4 bytes -/
structure StrategiesGroupStatusMessage where
  exchangeId : Alpha 1
  groupOfTheComplexOrderInstrument : Alpha 2
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace StrategiesGroupStatusMessage

def encode (message : StrategiesGroupStatusMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.groupOfTheComplexOrderInstrument
    ++ (GroupStatus.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (StrategiesGroupStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (groupOfTheComplexOrderInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ exchangeId, groupOfTheComplexOrderInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : StrategiesGroupStatusMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : StrategiesGroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategiesGroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end StrategiesGroupStatusMessage

/-- Market Depth Level: 29 bytes -/
structure MarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace MarketDepthLevel

def encode (message : MarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (MarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPrice, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPrice, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : MarketDepthLevel) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDepthLevel

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevels bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, instrumentDescription, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 284 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, InstrumentDescription.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 29 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Complex Market Depth Level: 31 bytes -/
structure ComplexMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceSign : Alpha 1
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : AskPriceSign
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace ComplexMarketDepthLevel

def encode (message : ComplexMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))))

def decode (bytes : List UInt8) : Option (ComplexMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPrice, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceSign, askPrice, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : ComplexMarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, Alpha.encode_length, AskPriceSign.encode_length]

theorem encode_length_pos (message : ComplexMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
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
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexMarketDepthLevel

/-- Complex Order Market Depth Message -/
structure ComplexOrderMarketDepthMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  instrumentStatusMarker : InstrumentStatusMarker
  complexMarketDepthLevel : Digited 1 ComplexMarketDepthLevel
  deriving DecidableEq, Repr

namespace ComplexOrderMarketDepthMessage

def encode (message : ComplexOrderMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.complexMarketDepthLevel.val.length
    ++ (encodeMany ComplexMarketDepthLevel.encode message.complexMarketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (ComplexOrderMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (complexMarketDepthLevel_, bytes) ← decodeMany ComplexMarketDepthLevel.decode numberOfLevels bytes
  if fits_complexMarketDepthLevel : complexMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, complexOrderInstrumentSymbol, instrumentStatusMarker, complexMarketDepthLevel := ⟨complexMarketDepthLevel_, fits_complexMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexOrderMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexOrderMarketDepthMessage) : (encode message).length ≤ 312 := by
  have bound_complexMarketDepthLevel := message.complexMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const ComplexMarketDepthLevel.encode 31 ComplexMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexOrderMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.complexMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany ComplexMarketDepthLevel.encode ComplexMarketDepthLevel.decode ComplexMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexMarketDepthLevel.length_lt]
  rfl

end ComplexOrderMarketDepthMessage

/-- Option Trade Cancellation Message: 57 bytes -/
structure OptionTradeCancellationMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 6
  openInterest : Alpha 7
  filler1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker)))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  pure ({ exchangeId, instrumentDescription, volume, tradePrice, tradePriceFractionIndicator, filler6, timestamp, openInterest, filler1, priceIndicatorMarker }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PriceIndicatorMarker.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Complex Order Trade Cancellation Message: 60 bytes -/
structure ComplexOrderTradeCancellationMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 6
  priceIndicatorMarker : PriceIndicatorMarker
  deriving DecidableEq, Repr

namespace ComplexOrderTradeCancellationMessage

def encode (message : ComplexOrderTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, filler6, timestamp, priceIndicatorMarker }, bytes)

@[simp] theorem encode_length (message : ComplexOrderTradeCancellationMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : ComplexOrderTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PriceIndicatorMarker.decode_encode, some_bind]
  rfl

end ComplexOrderTradeCancellationMessage

/-- Market Flow Indicator: 2 bytes -/
structure MarketFlowIndicator where
  typeOfInstrument : TypeOfInstrument
  typeOfUnderlying : TypeOfUnderlying
  deriving DecidableEq, Repr

namespace MarketFlowIndicator

def encode (message : MarketFlowIndicator) : List UInt8 :=
  TypeOfInstrument.encode message.typeOfInstrument
    ++ (TypeOfUnderlying.encode message.typeOfUnderlying)

def decode (bytes : List UInt8) : Option (MarketFlowIndicator × List UInt8) := do
  let (typeOfInstrument, bytes) ← TypeOfInstrument.decode bytes
  let (typeOfUnderlying, bytes) ← TypeOfUnderlying.decode bytes
  pure ({ typeOfInstrument, typeOfUnderlying }, bytes)

@[simp] theorem encode_length (message : MarketFlowIndicator) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, TypeOfInstrument.encode_length, TypeOfUnderlying.encode_length]

theorem encode_length_pos (message : MarketFlowIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketFlowIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TypeOfInstrument.decode_encode, some_bind]
  dsimp only
  rw [TypeOfUnderlying.decode_encode, some_bind]
  rfl

end MarketFlowIndicator

/-- Option Marker: 2 bytes -/
structure OptionMarker where
  typeOfMarket : Alpha 1
  typeOfOptions : TypeOfOptions
  deriving DecidableEq, Repr

namespace OptionMarker

def encode (message : OptionMarker) : List UInt8 :=
  Alpha.encode message.typeOfMarket
    ++ (TypeOfOptions.encode message.typeOfOptions)

def decode (bytes : List UInt8) : Option (OptionMarker × List UInt8) := do
  let (typeOfMarket, bytes) ← Alpha.decode 1 bytes
  let (typeOfOptions, bytes) ← TypeOfOptions.decode bytes
  pure ({ typeOfMarket, typeOfOptions }, bytes)

@[simp] theorem encode_length (message : OptionMarker) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TypeOfOptions.encode_length]

theorem encode_length_pos (message : OptionMarker) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionMarker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TypeOfOptions.decode_encode, some_bind]
  rfl

end OptionMarker

/-- Option Instrument Keys Message: 108 bytes -/
structure OptionInstrumentKeysMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPrice : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  optionType : OptionType
  marketFlowIndicator : MarketFlowIndicator
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : OptionMarker
  underlyingSymbolRoot : Alpha 10
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPrice
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (MarketFlowIndicator.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (OptionMarker.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRoot)))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPrice, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← MarketFlowIndicator.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← OptionMarker.decode bytes
  let (underlyingSymbolRoot, bytes) ← Alpha.decode 10 bytes
  pure ({ exchangeId, instrumentDescription, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPrice, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRoot }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, OptionType.encode_length, MarketFlowIndicator.encode_length, OptionMarker.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketFlowIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Instrument Leg: 39 bytes -/
structure InstrumentLeg where
  legRatioSign : LegRatioSign
  legRatio : Alpha 8
  legSymbol : Alpha 30
  deriving DecidableEq, Repr

namespace InstrumentLeg

def encode (message : InstrumentLeg) : List UInt8 :=
  LegRatioSign.encode message.legRatioSign
    ++ (Alpha.encode message.legRatio
    ++ (Alpha.encode message.legSymbol))

def decode (bytes : List UInt8) : Option (InstrumentLeg × List UInt8) := do
  let (legRatioSign, bytes) ← LegRatioSign.decode bytes
  let (legRatio, bytes) ← Alpha.decode 8 bytes
  let (legSymbol, bytes) ← Alpha.decode 30 bytes
  pure ({ legRatioSign, legRatio, legSymbol }, bytes)

@[simp] theorem encode_length (message : InstrumentLeg) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, LegRatioSign.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegRatioSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentLeg

/-- Complex Order Instrument Keys Message -/
structure ComplexOrderInstrumentKeysMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  expiryYear : Alpha 2
  deliveryMonth : DeliveryMonth
  expiryDay : Alpha 2
  maxNumberOfContractsPerOrder : Alpha 6
  minNumberOfContractsPerOrder : Alpha 6
  maxThresholdPriceSign : MaxThresholdPriceSign
  maxThresholdPrice : Alpha 6
  maxThresholdPriceFractionIndicator : Alpha 1
  minThresholdPriceSign : MinThresholdPriceSign
  minThresholdPrice : Alpha 6
  minThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  filler2 : Alpha 2
  group : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  complexOrderInstrumentAllowImplied : ComplexOrderInstrumentAllowImplied
  instrumentLeg : Digited 2 InstrumentLeg
  deriving DecidableEq, Repr

namespace ComplexOrderInstrumentKeysMessage

def encode (message : ComplexOrderInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.expiryYear
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maxNumberOfContractsPerOrder
    ++ (Alpha.encode message.minNumberOfContractsPerOrder
    ++ (MaxThresholdPriceSign.encode message.maxThresholdPriceSign
    ++ (Alpha.encode message.maxThresholdPrice
    ++ (Alpha.encode message.maxThresholdPriceFractionIndicator
    ++ (MinThresholdPriceSign.encode message.minThresholdPriceSign
    ++ (Alpha.encode message.minThresholdPrice
    ++ (Alpha.encode message.minThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (ComplexOrderInstrumentAllowImplied.encode message.complexOrderInstrumentAllowImplied
    ++ (encodeDigits 2 message.instrumentLeg.val.length
    ++ (encodeMany InstrumentLeg.encode message.instrumentLeg.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maxNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maxThresholdPriceSign, bytes) ← MaxThresholdPriceSign.decode bytes
  let (maxThresholdPrice, bytes) ← Alpha.decode 6 bytes
  let (maxThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minThresholdPriceSign, bytes) ← MinThresholdPriceSign.decode bytes
  let (minThresholdPrice, bytes) ← Alpha.decode 6 bytes
  let (minThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (complexOrderInstrumentAllowImplied, bytes) ← ComplexOrderInstrumentAllowImplied.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (instrumentLeg_, bytes) ← decodeMany InstrumentLeg.decode numberOfLegs bytes
  if fits_instrumentLeg : instrumentLeg_.length < 10 ^ 2 then
    pure ({ exchangeId, complexOrderInstrumentSymbol, expiryYear, deliveryMonth, expiryDay, maxNumberOfContractsPerOrder, minNumberOfContractsPerOrder, maxThresholdPriceSign, maxThresholdPrice, maxThresholdPriceFractionIndicator, minThresholdPriceSign, minThresholdPrice, minThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, filler2, group, instrument, instrumentExternalCode, complexOrderInstrumentAllowImplied, instrumentLeg := ⟨instrumentLeg_, fits_instrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexOrderInstrumentKeysMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexOrderInstrumentKeysMessage) : (encode message).length ≤ 3973 := by
  have bound_instrumentLeg := message.instrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, DeliveryMonth.encode_length, MaxThresholdPriceSign.encode_length, MinThresholdPriceSign.encode_length, ComplexOrderInstrumentAllowImplied.encode_length, encodeDigits_length, encodeMany_length_const InstrumentLeg.encode 39 InstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexOrderInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaxThresholdPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinThresholdPriceSign.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ComplexOrderInstrumentAllowImplied.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.instrumentLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany InstrumentLeg.encode InstrumentLeg.decode InstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentLeg.length_lt]
  rfl

end ComplexOrderInstrumentKeysMessage

/-- Bulletins Message: 82 bytes -/
structure BulletinsMessage where
  filler1 : Alpha 1
  bulletinType : BulletinType
  bulletinContents : Alpha 79
  continueMarker : ContinueMarker
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  Alpha.encode message.filler1
    ++ (BulletinType.encode message.bulletinType
    ++ (Alpha.encode message.bulletinContents
    ++ (ContinueMarker.encode message.continueMarker)))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← BulletinType.decode bytes
  let (bulletinContents, bytes) ← Alpha.decode 79 bytes
  let (continueMarker, bytes) ← ContinueMarker.decode bytes
  pure ({ filler1, bulletinType, bulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : BulletinsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BulletinType.encode_length, ContinueMarker.encode_length]

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BulletinType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ContinueMarker.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- Option Summary Message: 116 bytes -/
structure OptionSummaryMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openInterest : Alpha 7
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  optionMarker : OptionMarker
  underlyingSymbol : Alpha 10
  referencePrice : Alpha 6
  referencePriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (OptionMarker.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.referencePrice
    ++ (Alpha.encode message.referencePriceFractionIndicator)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionMarker, bytes) ← OptionMarker.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 10 bytes
  let (referencePrice, bytes) ← Alpha.decode 6 bytes
  let (referencePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, instrumentDescription, bidPrice, bidPriceFractionIndicator, bidSize, askPrice, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, optionMarker, underlyingSymbol, referencePrice, referencePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, Tick.encode_length, NetChangeSign.encode_length, OptionMarker.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Complex Order Summary Message: 105 bytes -/
structure ComplexOrderSummaryMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPrice : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPrice : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPriceSign : Alpha 1
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openPriceSign : OpenPriceSign
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPriceSign : HighPriceSign
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPriceSign : LowPriceSign
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  netChangeSign : NetChangeSign
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  deriving DecidableEq, Repr

namespace ComplexOrderSummaryMessage

def encode (message : ComplexOrderSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPriceSign
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (OpenPriceSign.encode message.openPriceSign
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (HighPriceSign.encode message.highPriceSign
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (LowPriceSign.encode message.lowPriceSign
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ComplexOrderSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPrice, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPrice, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPriceSign, bytes) ← OpenPriceSign.decode bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPriceSign, bytes) ← HighPriceSign.decode bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPriceSign, bytes) ← LowPriceSign.decode bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, bidPriceSign, bidPrice, bidPriceFractionIndicator, bidSize, askPriceSign, askPrice, askPriceFractionIndicator, askSize, lastPriceSign, lastPrice, lastPriceFractionIndicator, openPriceSign, openPrice, openPriceFractionIndicator, highPriceSign, highPrice, highPriceFractionIndicator, lowPriceSign, lowPrice, lowPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume }, bytes)

@[simp] theorem encode_length (message : ComplexOrderSummaryMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskPriceSign.encode_length, OpenPriceSign.encode_length, HighPriceSign.encode_length, LowPriceSign.encode_length, NetChangeSign.encode_length]

theorem encode_length_pos (message : ComplexOrderSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ComplexOrderSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexOrderSummaryMessage

/-- Beginning Of Options Summary Message: 1 bytes -/
structure BeginningOfOptionsSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Complex Order Summary Message: 1 bytes -/
structure BeginningOfComplexOrderSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfComplexOrderSummaryMessage

def encode (message : BeginningOfComplexOrderSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfComplexOrderSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfComplexOrderSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfComplexOrderSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfComplexOrderSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfComplexOrderSummaryMessage

/-- End Of Sales Message: 7 bytes -/
structure EndOfSalesMessage where
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Option Improvement Process Beginning Message: 73 bytes -/
structure OptionImprovementProcessBeginningMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  improvementPhaseSequentialNumber : Alpha 6
  initialOrderPrice : Alpha 6
  initialOrderPriceFractionIndicator : Alpha 1
  initialOrderQuantity : Alpha 8
  initialOrderSide : InitialOrderSide
  improvementPhaseExpiryTime : Alpha 8
  improvementProcessExpiryDuration : Alpha 4
  minimumQuantityForImprovementOrder : Alpha 8
  percentageAssuredToInitialOrder : Alpha 8
  auctionType : AuctionType
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace OptionImprovementProcessBeginningMessage

def encode (message : OptionImprovementProcessBeginningMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (Alpha.encode message.initialOrderPrice
    ++ (Alpha.encode message.initialOrderPriceFractionIndicator
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.improvementPhaseExpiryTime
    ++ (Alpha.encode message.improvementProcessExpiryDuration
    ++ (Alpha.encode message.minimumQuantityForImprovementOrder
    ++ (Alpha.encode message.percentageAssuredToInitialOrder
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.filler1))))))))))))

def decode (bytes : List UInt8) : Option (OptionImprovementProcessBeginningMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (initialOrderPrice, bytes) ← Alpha.decode 6 bytes
  let (initialOrderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (improvementPhaseExpiryTime, bytes) ← Alpha.decode 8 bytes
  let (improvementProcessExpiryDuration, bytes) ← Alpha.decode 4 bytes
  let (minimumQuantityForImprovementOrder, bytes) ← Alpha.decode 8 bytes
  let (percentageAssuredToInitialOrder, bytes) ← Alpha.decode 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, instrumentDescription, improvementPhaseSequentialNumber, initialOrderPrice, initialOrderPriceFractionIndicator, initialOrderQuantity, initialOrderSide, improvementPhaseExpiryTime, improvementProcessExpiryDuration, minimumQuantityForImprovementOrder, percentageAssuredToInitialOrder, auctionType, filler1 }, bytes)

@[simp] theorem encode_length (message : OptionImprovementProcessBeginningMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, InitialOrderSide.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : OptionImprovementProcessBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionImprovementProcessBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionImprovementProcessBeginningMessage

/-- Complex Order Improvement Process Beginning Message Message: 83 bytes -/
structure ComplexOrderImprovementProcessBeginningMessageMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  improvementPhaseSequentialNumber : Alpha 6
  initialOrderPriceSign : InitialOrderPriceSign
  initialOrderPrice : Alpha 6
  initialOrderPriceFractionIndicator : Alpha 1
  initialOrderQuantity : Alpha 8
  initialOrderSide : InitialOrderSide
  improvementPhaseExpiryTime : Alpha 8
  improvementProcessExpiryDuration : Alpha 4
  minimumQuantityForImprovementOrder : Alpha 8
  percentageAssuredToInitialOrder : Alpha 8
  auctionType : AuctionType
  deriving DecidableEq, Repr

namespace ComplexOrderImprovementProcessBeginningMessageMessage

def encode (message : ComplexOrderImprovementProcessBeginningMessageMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (InitialOrderPriceSign.encode message.initialOrderPriceSign
    ++ (Alpha.encode message.initialOrderPrice
    ++ (Alpha.encode message.initialOrderPriceFractionIndicator
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.improvementPhaseExpiryTime
    ++ (Alpha.encode message.improvementProcessExpiryDuration
    ++ (Alpha.encode message.minimumQuantityForImprovementOrder
    ++ (Alpha.encode message.percentageAssuredToInitialOrder
    ++ (AuctionType.encode message.auctionType))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderImprovementProcessBeginningMessageMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (initialOrderPriceSign, bytes) ← InitialOrderPriceSign.decode bytes
  let (initialOrderPrice, bytes) ← Alpha.decode 6 bytes
  let (initialOrderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (improvementPhaseExpiryTime, bytes) ← Alpha.decode 8 bytes
  let (improvementProcessExpiryDuration, bytes) ← Alpha.decode 4 bytes
  let (minimumQuantityForImprovementOrder, bytes) ← Alpha.decode 8 bytes
  let (percentageAssuredToInitialOrder, bytes) ← Alpha.decode 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, improvementPhaseSequentialNumber, initialOrderPriceSign, initialOrderPrice, initialOrderPriceFractionIndicator, initialOrderQuantity, initialOrderSide, improvementPhaseExpiryTime, improvementProcessExpiryDuration, minimumQuantityForImprovementOrder, percentageAssuredToInitialOrder, auctionType }, bytes)

@[simp] theorem encode_length (message : ComplexOrderImprovementProcessBeginningMessageMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InitialOrderPriceSign.encode_length, InitialOrderSide.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : ComplexOrderImprovementProcessBeginningMessageMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderImprovementProcessBeginningMessageMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [AuctionType.decode_encode, some_bind]
  rfl

end ComplexOrderImprovementProcessBeginningMessageMessage

/-- Market Sheet Initial And Improvement Order Message: 64 bytes -/
structure MarketSheetInitialAndImprovementOrderMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  orderSide : OrderSide
  typeOfOrder : TypeOfOrder
  filler1 : Alpha 1
  limitFractionIndicator : Alpha 1
  orderQuantity : Alpha 8
  orderSequenceNumber : Alpha 6
  improvementPhaseSequentialNumber : Alpha 6
  typeOfClearingAccount : TypeOfClearingAccount
  secondFiller1 : Alpha 1
  endOfTheExposition : Alpha 8
  auctionType : AuctionType
  firmId : Alpha 4
  cmta : Alpha 4
  deriving DecidableEq, Repr

namespace MarketSheetInitialAndImprovementOrderMessage

def encode (message : MarketSheetInitialAndImprovementOrderMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (OrderSide.encode message.orderSide
    ++ (TypeOfOrder.encode message.typeOfOrder
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.limitFractionIndicator
    ++ (Alpha.encode message.orderQuantity
    ++ (Alpha.encode message.orderSequenceNumber
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (TypeOfClearingAccount.encode message.typeOfClearingAccount
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.endOfTheExposition
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.cmta))))))))))))))

def decode (bytes : List UInt8) : Option (MarketSheetInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (typeOfOrder, bytes) ← TypeOfOrder.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (limitFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderSequenceNumber, bytes) ← Alpha.decode 6 bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (typeOfClearingAccount, bytes) ← TypeOfClearingAccount.decode bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (endOfTheExposition, bytes) ← Alpha.decode 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (cmta, bytes) ← Alpha.decode 4 bytes
  pure ({ exchangeId, instrumentDescription, orderSide, typeOfOrder, filler1, limitFractionIndicator, orderQuantity, orderSequenceNumber, improvementPhaseSequentialNumber, typeOfClearingAccount, secondFiller1, endOfTheExposition, auctionType, firmId, cmta }, bytes)

@[simp] theorem encode_length (message : MarketSheetInitialAndImprovementOrderMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, OrderSide.encode_length, TypeOfOrder.encode_length, TypeOfClearingAccount.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : MarketSheetInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSheetInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfOrder.decode_encode, some_bind]
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
  rw [List.append_assoc, TypeOfClearingAccount.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketSheetInitialAndImprovementOrderMessage

/-- Complex Order Market Sheet Initial And Improvement Order Message: 75 bytes -/
structure ComplexOrderMarketSheetInitialAndImprovementOrderMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  orderSide : OrderSide
  typeOfOrder : TypeOfOrder
  limitEnteredForAnOrderSign : LimitEnteredForAnOrderSign
  filler1 : Alpha 1
  limitFractionIndicator : Alpha 1
  orderQuantity : Alpha 8
  orderSequenceNumber : Alpha 6
  improvementPhaseSequentialNumber : Alpha 6
  typeOfClearingAccount : TypeOfClearingAccount
  secondFiller1 : Alpha 1
  endOfTheExposition : Alpha 8
  auctionType : AuctionType
  firmId : Alpha 4
  cmta : Alpha 4
  deriving DecidableEq, Repr

namespace ComplexOrderMarketSheetInitialAndImprovementOrderMessage

def encode (message : ComplexOrderMarketSheetInitialAndImprovementOrderMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (OrderSide.encode message.orderSide
    ++ (TypeOfOrder.encode message.typeOfOrder
    ++ (LimitEnteredForAnOrderSign.encode message.limitEnteredForAnOrderSign
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.limitFractionIndicator
    ++ (Alpha.encode message.orderQuantity
    ++ (Alpha.encode message.orderSequenceNumber
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (TypeOfClearingAccount.encode message.typeOfClearingAccount
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.endOfTheExposition
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.cmta)))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderMarketSheetInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (typeOfOrder, bytes) ← TypeOfOrder.decode bytes
  let (limitEnteredForAnOrderSign, bytes) ← LimitEnteredForAnOrderSign.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (limitFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderSequenceNumber, bytes) ← Alpha.decode 6 bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (typeOfClearingAccount, bytes) ← TypeOfClearingAccount.decode bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (endOfTheExposition, bytes) ← Alpha.decode 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (cmta, bytes) ← Alpha.decode 4 bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, orderSide, typeOfOrder, limitEnteredForAnOrderSign, filler1, limitFractionIndicator, orderQuantity, orderSequenceNumber, improvementPhaseSequentialNumber, typeOfClearingAccount, secondFiller1, endOfTheExposition, auctionType, firmId, cmta }, bytes)

@[simp] theorem encode_length (message : ComplexOrderMarketSheetInitialAndImprovementOrderMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, OrderSide.encode_length, TypeOfOrder.encode_length, LimitEnteredForAnOrderSign.encode_length, TypeOfClearingAccount.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : ComplexOrderMarketSheetInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderMarketSheetInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfOrder.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitEnteredForAnOrderSign.decode_encode, some_bind]
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
  rw [List.append_assoc, TypeOfClearingAccount.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexOrderMarketSheetInitialAndImprovementOrderMessage

/-- Initial And Improvement Order Message: 36 bytes -/
structure InitialAndImprovementOrderMessage where
  exchangeId : Alpha 1
  instrumentDescription : InstrumentDescription
  deletionType : DeletionType
  orderSequenceNumber : Alpha 6
  improvementOrderSide : ImprovementOrderSide
  improvementPhaseSequentialNumber : Alpha 6
  auctionType : AuctionType
  deriving DecidableEq, Repr

namespace InitialAndImprovementOrderMessage

def encode (message : InitialAndImprovementOrderMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (InstrumentDescription.encode message.instrumentDescription
    ++ (DeletionType.encode message.deletionType
    ++ (Alpha.encode message.orderSequenceNumber
    ++ (ImprovementOrderSide.encode message.improvementOrderSide
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (AuctionType.encode message.auctionType))))))

def decode (bytes : List UInt8) : Option (InitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (instrumentDescription, bytes) ← InstrumentDescription.decode bytes
  let (deletionType, bytes) ← DeletionType.decode bytes
  let (orderSequenceNumber, bytes) ← Alpha.decode 6 bytes
  let (improvementOrderSide, bytes) ← ImprovementOrderSide.decode bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  pure ({ exchangeId, instrumentDescription, deletionType, orderSequenceNumber, improvementOrderSide, improvementPhaseSequentialNumber, auctionType }, bytes)

@[simp] theorem encode_length (message : InitialAndImprovementOrderMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentDescription.encode_length, DeletionType.encode_length, ImprovementOrderSide.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : InitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDescription.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeletionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImprovementOrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [AuctionType.decode_encode, some_bind]
  rfl

end InitialAndImprovementOrderMessage

/-- Complex Order Initial And Improvement Order Message: 46 bytes -/
structure ComplexOrderInitialAndImprovementOrderMessage where
  exchangeId : Alpha 1
  complexOrderInstrumentSymbol : Alpha 30
  deletionType : DeletionType
  orderSequenceNumber : Alpha 6
  orderSide : OrderSide
  improvementPhaseSequentialNumber : Alpha 6
  auctionType : AuctionType
  deriving DecidableEq, Repr

namespace ComplexOrderInitialAndImprovementOrderMessage

def encode (message : ComplexOrderInitialAndImprovementOrderMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.complexOrderInstrumentSymbol
    ++ (DeletionType.encode message.deletionType
    ++ (Alpha.encode message.orderSequenceNumber
    ++ (OrderSide.encode message.orderSide
    ++ (Alpha.encode message.improvementPhaseSequentialNumber
    ++ (AuctionType.encode message.auctionType))))))

def decode (bytes : List UInt8) : Option (ComplexOrderInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (complexOrderInstrumentSymbol, bytes) ← Alpha.decode 30 bytes
  let (deletionType, bytes) ← DeletionType.decode bytes
  let (orderSequenceNumber, bytes) ← Alpha.decode 6 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (improvementPhaseSequentialNumber, bytes) ← Alpha.decode 6 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  pure ({ exchangeId, complexOrderInstrumentSymbol, deletionType, orderSequenceNumber, orderSide, improvementPhaseSequentialNumber, auctionType }, bytes)

@[simp] theorem encode_length (message : ComplexOrderInitialAndImprovementOrderMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DeletionType.encode_length, OrderSide.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : ComplexOrderInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeletionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [AuctionType.decode_encode, some_bind]
  rfl

end ComplexOrderInitialAndImprovementOrderMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  | systemTimestampMessage (message : SystemTimestampMessage) -- "Z " 0x5A20
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | complexOrderInstrumentTradeMessage (message : ComplexOrderInstrumentTradeMessage) -- "CS" 0x4353
  | optionRequestForQuoteMessage (message : OptionRequestForQuoteMessage) -- "D " 0x4420
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | complexOrderQuoteMessage (message : ComplexOrderQuoteMessage) -- "FS" 0x4653
  | groupOpeningTimeMessage (message : GroupOpeningTimeMessage) -- "GC" 0x4743
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | strategiesGroupStatusMessage (message : StrategiesGroupStatusMessage) -- "GS" 0x4753
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | complexOrderMarketDepthMessage (message : ComplexOrderMarketDepthMessage) -- "HS" 0x4853
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | complexOrderTradeCancellationMessage (message : ComplexOrderTradeCancellationMessage) -- "IS" 0x4953
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | complexOrderInstrumentKeysMessage (message : ComplexOrderInstrumentKeysMessage) -- "JS" 0x4A53
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | complexOrderSummaryMessage (message : ComplexOrderSummaryMessage) -- "NS" 0x4E53
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfComplexOrderSummaryMessage (message : BeginningOfComplexOrderSummaryMessage) -- "QS" 0x5153
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | optionImprovementProcessBeginningMessage (message : OptionImprovementProcessBeginningMessage) -- "M " 0x4D20
  | complexOrderImprovementProcessBeginningMessageMessage (message : ComplexOrderImprovementProcessBeginningMessageMessage) -- "MS" 0x4D53
  | marketSheetInitialAndImprovementOrderMessage (message : MarketSheetInitialAndImprovementOrderMessage) -- "O " 0x4F20
  | complexOrderMarketSheetInitialAndImprovementOrderMessage (message : ComplexOrderMarketSheetInitialAndImprovementOrderMessage) -- "OS" 0x4F53
  | initialAndImprovementOrderMessage (message : InitialAndImprovementOrderMessage) -- "T " 0x5420
  | complexOrderInitialAndImprovementOrderMessage (message : ComplexOrderInitialAndImprovementOrderMessage) -- "TS" 0x5453
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048
  | .systemTimestampMessage _ => 23072
  | .optionTradeMessage _ => 17184
  | .complexOrderInstrumentTradeMessage _ => 17235
  | .optionRequestForQuoteMessage _ => 17440
  | .optionQuoteMessage _ => 17952
  | .complexOrderQuoteMessage _ => 18003
  | .groupOpeningTimeMessage _ => 18243
  | .groupStatusMessage _ => 18258
  | .strategiesGroupStatusMessage _ => 18259
  | .optionMarketDepthMessage _ => 18464
  | .complexOrderMarketDepthMessage _ => 18515
  | .optionTradeCancellationMessage _ => 18720
  | .complexOrderTradeCancellationMessage _ => 18771
  | .optionInstrumentKeysMessage _ => 18976
  | .complexOrderInstrumentKeysMessage _ => 19027
  | .bulletinsMessage _ => 19488
  | .optionSummaryMessage _ => 20000
  | .complexOrderSummaryMessage _ => 20051
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfComplexOrderSummaryMessage _ => 20819
  | .endOfSalesMessage _ => 21280
  | .optionImprovementProcessBeginningMessage _ => 19744
  | .complexOrderImprovementProcessBeginningMessageMessage _ => 19795
  | .marketSheetInitialAndImprovementOrderMessage _ => 20256
  | .complexOrderMarketSheetInitialAndImprovementOrderMessage _ => 20307
  | .initialAndImprovementOrderMessage _ => 21536
  | .complexOrderInitialAndImprovementOrderMessage _ => 21587

def encode : MessageBody → List UInt8
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message
  | .systemTimestampMessage message => SystemTimestampMessage.encode message
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .complexOrderInstrumentTradeMessage message => ComplexOrderInstrumentTradeMessage.encode message
  | .optionRequestForQuoteMessage message => OptionRequestForQuoteMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .complexOrderQuoteMessage message => ComplexOrderQuoteMessage.encode message
  | .groupOpeningTimeMessage message => GroupOpeningTimeMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .strategiesGroupStatusMessage message => StrategiesGroupStatusMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .complexOrderMarketDepthMessage message => ComplexOrderMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .complexOrderTradeCancellationMessage message => ComplexOrderTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .complexOrderInstrumentKeysMessage message => ComplexOrderInstrumentKeysMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .complexOrderSummaryMessage message => ComplexOrderSummaryMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfComplexOrderSummaryMessage message => BeginningOfComplexOrderSummaryMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .optionImprovementProcessBeginningMessage message => OptionImprovementProcessBeginningMessage.encode message
  | .complexOrderImprovementProcessBeginningMessageMessage message => ComplexOrderImprovementProcessBeginningMessageMessage.encode message
  | .marketSheetInitialAndImprovementOrderMessage message => MarketSheetInitialAndImprovementOrderMessage.encode message
  | .complexOrderMarketSheetInitialAndImprovementOrderMessage message => ComplexOrderMarketSheetInitialAndImprovementOrderMessage.encode message
  | .initialAndImprovementOrderMessage message => InitialAndImprovementOrderMessage.encode message
  | .complexOrderInitialAndImprovementOrderMessage message => ComplexOrderInitialAndImprovementOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3973 := by
  cases message with
  | endOfTransmissionMessage inner =>
    simp only [encode, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [encode, CircuitAssuranceMessage.encode_length]
    omega
  | systemTimestampMessage inner =>
    simp only [encode, SystemTimestampMessage.encode_length]
    omega
  | optionTradeMessage inner =>
    simp only [encode, OptionTradeMessage.encode_length]
    omega
  | complexOrderInstrumentTradeMessage inner =>
    simp only [encode, ComplexOrderInstrumentTradeMessage.encode_length]
    omega
  | optionRequestForQuoteMessage inner =>
    simp only [encode, OptionRequestForQuoteMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [encode, OptionQuoteMessage.encode_length]
    omega
  | complexOrderQuoteMessage inner =>
    simp only [encode, ComplexOrderQuoteMessage.encode_length]
    omega
  | groupOpeningTimeMessage inner =>
    simp only [encode, GroupOpeningTimeMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | strategiesGroupStatusMessage inner =>
    simp only [encode, StrategiesGroupStatusMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | complexOrderMarketDepthMessage inner =>
    have bound_inner := ComplexOrderMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | complexOrderTradeCancellationMessage inner =>
    simp only [encode, ComplexOrderTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [encode, OptionInstrumentKeysMessage.encode_length]
    omega
  | complexOrderInstrumentKeysMessage inner =>
    have bound_inner := ComplexOrderInstrumentKeysMessage.encode_length_le inner
    simp only [encode]
    omega
  | bulletinsMessage inner =>
    simp only [encode, BulletinsMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [encode, OptionSummaryMessage.encode_length]
    omega
  | complexOrderSummaryMessage inner =>
    simp only [encode, ComplexOrderSummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfComplexOrderSummaryMessage inner =>
    simp only [encode, BeginningOfComplexOrderSummaryMessage.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [encode, EndOfSalesMessage.encode_length]
    omega
  | optionImprovementProcessBeginningMessage inner =>
    simp only [encode, OptionImprovementProcessBeginningMessage.encode_length]
    omega
  | complexOrderImprovementProcessBeginningMessageMessage inner =>
    simp only [encode, ComplexOrderImprovementProcessBeginningMessageMessage.encode_length]
    omega
  | marketSheetInitialAndImprovementOrderMessage inner =>
    simp only [encode, MarketSheetInitialAndImprovementOrderMessage.encode_length]
    omega
  | complexOrderMarketSheetInitialAndImprovementOrderMessage inner =>
    simp only [encode, ComplexOrderMarketSheetInitialAndImprovementOrderMessage.encode_length]
    omega
  | initialAndImprovementOrderMessage inner =>
    simp only [encode, InitialAndImprovementOrderMessage.encode_length]
    omega
  | complexOrderInitialAndImprovementOrderMessage inner =>
    simp only [encode, ComplexOrderInitialAndImprovementOrderMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else if tag = 23072 then (SystemTimestampMessage.decode bytes).map fun (message, rest) => (.systemTimestampMessage message, rest)
  else if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17235 then (ComplexOrderInstrumentTradeMessage.decode bytes).map fun (message, rest) => (.complexOrderInstrumentTradeMessage message, rest)
  else if tag = 17440 then (OptionRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.optionRequestForQuoteMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 18003 then (ComplexOrderQuoteMessage.decode bytes).map fun (message, rest) => (.complexOrderQuoteMessage message, rest)
  else if tag = 18243 then (GroupOpeningTimeMessage.decode bytes).map fun (message, rest) => (.groupOpeningTimeMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (StrategiesGroupStatusMessage.decode bytes).map fun (message, rest) => (.strategiesGroupStatusMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18515 then (ComplexOrderMarketDepthMessage.decode bytes).map fun (message, rest) => (.complexOrderMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18771 then (ComplexOrderTradeCancellationMessage.decode bytes).map fun (message, rest) => (.complexOrderTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19027 then (ComplexOrderInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.complexOrderInstrumentKeysMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20051 then (ComplexOrderSummaryMessage.decode bytes).map fun (message, rest) => (.complexOrderSummaryMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfComplexOrderSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfComplexOrderSummaryMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 19744 then (OptionImprovementProcessBeginningMessage.decode bytes).map fun (message, rest) => (.optionImprovementProcessBeginningMessage message, rest)
  else if tag = 19795 then (ComplexOrderImprovementProcessBeginningMessageMessage.decode bytes).map fun (message, rest) => (.complexOrderImprovementProcessBeginningMessageMessage message, rest)
  else if tag = 20256 then (MarketSheetInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.marketSheetInitialAndImprovementOrderMessage message, rest)
  else if tag = 20307 then (ComplexOrderMarketSheetInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.complexOrderMarketSheetInitialAndImprovementOrderMessage message, rest)
  else if tag = 21536 then (InitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.initialAndImprovementOrderMessage message, rest)
  else if tag = 21587 then (ComplexOrderInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.complexOrderInitialAndImprovementOrderMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  hsvfStx : BitVec 8
  sequenceNumber : Alpha 9
  messageBody : MessageBody
  hsvfEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.hsvfStx
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.hsvfEtx))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (hsvfStx, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (hsvfEtx, bytes) ← decodeUInt 1 bytes
  pure ({ hsvfStx, sequenceNumber, messageBody, hsvfEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3986 := by
  unfold encode
  cases message.messageBody with
  | endOfTransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CircuitAssuranceMessage.encode_length]
    omega
  | systemTimestampMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SystemTimestampMessage.encode_length]
    omega
  | optionTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeMessage.encode_length]
    omega
  | complexOrderInstrumentTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderInstrumentTradeMessage.encode_length]
    omega
  | optionRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRequestForQuoteMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionQuoteMessage.encode_length]
    omega
  | complexOrderQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderQuoteMessage.encode_length]
    omega
  | groupOpeningTimeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupOpeningTimeMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | strategiesGroupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategiesGroupStatusMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | complexOrderMarketDepthMessage inner =>
    have bound_inner := ComplexOrderMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | complexOrderTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInstrumentKeysMessage.encode_length]
    omega
  | complexOrderInstrumentKeysMessage inner =>
    have bound_inner := ComplexOrderInstrumentKeysMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | bulletinsMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BulletinsMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionSummaryMessage.encode_length]
    omega
  | complexOrderSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderSummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfComplexOrderSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfComplexOrderSummaryMessage.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfSalesMessage.encode_length]
    omega
  | optionImprovementProcessBeginningMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionImprovementProcessBeginningMessage.encode_length]
    omega
  | complexOrderImprovementProcessBeginningMessageMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderImprovementProcessBeginningMessageMessage.encode_length]
    omega
  | marketSheetInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MarketSheetInitialAndImprovementOrderMessage.encode_length]
    omega
  | complexOrderMarketSheetInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderMarketSheetInitialAndImprovementOrderMessage.encode_length]
    omega
  | initialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InitialAndImprovementOrderMessage.encode_length]
    omega
  | complexOrderInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ComplexOrderInitialAndImprovementOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.BoxBoxoptionsSolamulticastHsvfV18
