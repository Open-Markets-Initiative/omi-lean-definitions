import Wire

/-!
# The Securities Industry Automation Corporation Output v1.91

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Block Pad Byte pads to a 2 byte boundary: it is read as the bytes left to the end of the frame, fewer than 2, and the frame's length is trusted to keep the boundary.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCtsOutputCtaV191

/-- Retransmission Indicator: one byte code -/
def RetransmissionIndicator.codes : List UInt8 :=
  [0x4F, 0x56]

inductive RetransmissionIndicator where
  | original -- Original
  | retransmitted -- Retransmitted
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIndicator

def toByte : RetransmissionIndicator → UInt8
  | .original => 0x4F
  | .retransmitted => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionIndicator :=
  if byte = 0x4F then .original
  else .retransmitted

def ofByte (byte : UInt8) : RetransmissionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIndicator) : ofByte value.toByte = value := by
  cases value with
  | original => decide
  | retransmitted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetransmissionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIndicator

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive ParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cts -- Cts
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cts => 0x53
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cts
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cts => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantId

/-- Market Wide Circuit Breaker Level Indicator: one byte code -/
def MarketWideCircuitBreakerLevelIndicator.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33]

inductive MarketWideCircuitBreakerLevelIndicator where
  | notApplicable -- Not Applicable
  | level1Breached -- Level 1 Breached
  | level2Breached -- Level 2 Breached
  | level3Breached -- Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketWideCircuitBreakerLevelIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerLevelIndicator

def toByte : MarketWideCircuitBreakerLevelIndicator → UInt8
  | .notApplicable => 0x20
  | .level1Breached => 0x31
  | .level2Breached => 0x32
  | .level3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x31 then .level1Breached
  else if byte = 0x32 then .level2Breached
  else .level3Breached

def ofByte (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketWideCircuitBreakerLevelIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | level1Breached => decide
  | level2Breached => decide
  | level3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketWideCircuitBreakerLevelIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketWideCircuitBreakerLevelIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketWideCircuitBreakerLevelIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketWideCircuitBreakerLevelIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketWideCircuitBreakerLevelIndicator

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive InstrumentType where
  | ctaEligibleEquity -- Cta Eligible Equity
  | localIssue -- Local Issue
  | corporateBond -- Corporate Bond
  | governmentBond -- Government Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .ctaEligibleEquity => 0x30
  | .localIssue => 0x31
  | .corporateBond => 0x32
  | .governmentBond => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x30 then .ctaEligibleEquity
  else if byte = 0x31 then .localIssue
  else if byte = 0x32 then .corporateBond
  else .governmentBond

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | ctaEligibleEquity => decide
  | localIssue => decide
  | corporateBond => decide
  | governmentBond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Category 2: one byte code -/
def Category2.codes : List UInt8 :=
  [0x20, 0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive Category2 where
  | noReason -- No Reason
  | intermarketSweepOrder -- Intermarket Sweep Order
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | derivativelyPriced -- Derivatively Priced
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | reserved -- Reserved
  | correctedConsolidatedClosePriceAsPerListingMarket -- Corrected Consolidated Close Price As Per Listing Market
  | unlisted (byte : { byte : UInt8 // byte ∉ Category2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Category2

def toByte : Category2 → UInt8
  | .noReason => 0x20
  | .intermarketSweepOrder => 0x46
  | .marketCenterOpeningTrade => 0x4F
  | .derivativelyPriced => 0x34
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .qualifiedContingentTrade => 0x37
  | .reserved => 0x38
  | .correctedConsolidatedClosePriceAsPerListingMarket => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Category2 :=
  if byte = 0x20 then .noReason
  else if byte = 0x46 then .intermarketSweepOrder
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x34 then .derivativelyPriced
  else if byte = 0x35 then .marketCenterReopeningTrade
  else if byte = 0x36 then .marketCenterClosingTrade
  else if byte = 0x37 then .qualifiedContingentTrade
  else if byte = 0x38 then .reserved
  else .correctedConsolidatedClosePriceAsPerListingMarket

def ofByte (byte : UInt8) : Category2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Category2) : ofByte value.toByte = value := by
  cases value with
  | noReason => decide
  | intermarketSweepOrder => decide
  | marketCenterOpeningTrade => decide
  | derivativelyPriced => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | qualifiedContingentTrade => decide
  | reserved => decide
  | correctedConsolidatedClosePriceAsPerListingMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Category2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Category2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Category2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Category2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Category2

/-- Category 3: one byte code -/
def Category3.codes : List UInt8 :=
  [0x20, 0x4C, 0x54, 0x55, 0x5A]

inductive Category3 where
  | notExtendedHoursOrSoldOutOfSequence -- Not Extended Hours Or Sold Out Of Sequence
  | soldLast -- Sold Last
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursSold -- Extended Hours Sold
  | soldOutOfSequence -- Sold Out Of Sequence
  | unlisted (byte : { byte : UInt8 // byte ∉ Category3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Category3

def toByte : Category3 → UInt8
  | .notExtendedHoursOrSoldOutOfSequence => 0x20
  | .soldLast => 0x4C
  | .extendedHoursTrade => 0x54
  | .extendedHoursSold => 0x55
  | .soldOutOfSequence => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Category3 :=
  if byte = 0x20 then .notExtendedHoursOrSoldOutOfSequence
  else if byte = 0x4C then .soldLast
  else if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursSold
  else .soldOutOfSequence

def ofByte (byte : UInt8) : Category3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Category3) : ofByte value.toByte = value := by
  cases value with
  | notExtendedHoursOrSoldOutOfSequence => decide
  | soldLast => decide
  | extendedHoursTrade => decide
  | extendedHoursSold => decide
  | soldOutOfSequence => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Category3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Category3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Category3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Category3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Category3

/-- Category 4: one byte code -/
def Category4.codes : List UInt8 :=
  [0x20, 0x42, 0x45, 0x48, 0x49, 0x4B, 0x4D, 0x50, 0x51, 0x56, 0x58]

inductive Category4 where
  | noSroRequiredTradeDetail -- No Sro Required Trade Detail
  | averagePriceTrade -- Average Price Trade
  | automaticExecution -- Automatic Execution
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | rule127Or155 -- Rule 127 Or 155
  | marketCenterOfficialClose -- Market Center Official Close
  | priorReferencePrice -- Prior Reference Price
  | marketCenterOfficialOpen -- Market Center Official Open
  | contingentTrade -- Contingent Trade
  | crossTrade -- Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ Category4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Category4

def toByte : Category4 → UInt8
  | .noSroRequiredTradeDetail => 0x20
  | .averagePriceTrade => 0x42
  | .automaticExecution => 0x45
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .rule127Or155 => 0x4B
  | .marketCenterOfficialClose => 0x4D
  | .priorReferencePrice => 0x50
  | .marketCenterOfficialOpen => 0x51
  | .contingentTrade => 0x56
  | .crossTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Category4 :=
  if byte = 0x20 then .noSroRequiredTradeDetail
  else if byte = 0x42 then .averagePriceTrade
  else if byte = 0x45 then .automaticExecution
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4B then .rule127Or155
  else if byte = 0x4D then .marketCenterOfficialClose
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .marketCenterOfficialOpen
  else if byte = 0x56 then .contingentTrade
  else .crossTrade

def ofByte (byte : UInt8) : Category4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Category4) : ofByte value.toByte = value := by
  cases value with
  | noSroRequiredTradeDetail => decide
  | averagePriceTrade => decide
  | automaticExecution => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | rule127Or155 => decide
  | marketCenterOfficialClose => decide
  | priorReferencePrice => decide
  | marketCenterOfficialOpen => decide
  | contingentTrade => decide
  | crossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Category4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Category4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Category4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Category4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Category4

/-- Stop Stock Indicator: one byte code -/
def StopStockIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive StopStockIndicator where
  | notApplicable -- Not Applicable
  | stopStock -- Stop Stock
  | unlisted (byte : { byte : UInt8 // byte ∉ StopStockIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StopStockIndicator

def toByte : StopStockIndicator → UInt8
  | .notApplicable => 0x30
  | .stopStock => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StopStockIndicator :=
  if byte = 0x30 then .notApplicable
  else .stopStock

def ofByte (byte : UInt8) : StopStockIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StopStockIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | stopStock => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StopStockIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StopStockIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StopStockIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StopStockIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StopStockIndicator

/-- Trade Through Exempt Indicator: one byte code -/
def TradeThroughExemptIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive TradeThroughExemptIndicator where
  | notATradeThroughExemption -- Not A Trade Through Exemption
  | tradeThroughExemption -- Trade Through Exemption
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeThroughExemptIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeThroughExemptIndicator

def toByte : TradeThroughExemptIndicator → UInt8
  | .notATradeThroughExemption => 0x30
  | .tradeThroughExemption => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeThroughExemptIndicator :=
  if byte = 0x30 then .notATradeThroughExemption
  else .tradeThroughExemption

def ofByte (byte : UInt8) : TradeThroughExemptIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeThroughExemptIndicator) : ofByte value.toByte = value := by
  cases value with
  | notATradeThroughExemption => decide
  | tradeThroughExemption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeThroughExemptIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeThroughExemptIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeThroughExemptIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeThroughExemptIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeThroughExemptIndicator

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45]

inductive ShortSaleRestrictionIndicator where
  | notInEffect -- Not In Effect
  | activated -- Activated
  | continued -- Continued
  | deactivated -- Deactivated
  | restrictionInEffect -- Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .notInEffect => 0x20
  | .activated => 0x41
  | .continued => 0x43
  | .deactivated => 0x44
  | .restrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .notInEffect
  else if byte = 0x41 then .activated
  else if byte = 0x43 then .continued
  else if byte = 0x44 then .deactivated
  else .restrictionInEffect

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | notInEffect => decide
  | activated => decide
  | continued => decide
  | deactivated => decide
  | restrictionInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleRestrictionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleRestrictionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleRestrictionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleRestrictionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleRestrictionIndicator

/-- Trade Reporting Facility Id: one byte code -/
def TradeReportingFacilityId.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive TradeReportingFacilityId where
  | notApplicable -- Not Applicable
  | inactiveValueA -- Inactive Value A
  | finraNasdaqChicago -- Finra Nasdaq Chicago
  | inactiveValueC -- Inactive Value C
  | inactiveValueD -- Inactive Value D
  | inactiveValueI -- Inactive Value I
  | inactiveValueJ -- Inactive Value J
  | inactiveValueK -- Inactive Value K
  | inactiveValueM -- Inactive Value M
  | finraNyse -- Finra Nyse
  | inactiveValueP -- Inactive Value P
  | finraNasdaqCarteret -- Finra Nasdaq Carteret
  | inactiveValueV -- Inactive Value V
  | inactiveValueW -- Inactive Value W
  | inactiveValueX -- Inactive Value X
  | inactiveValueY -- Inactive Value Y
  | inactiveValueZ -- Inactive Value Z
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeReportingFacilityId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeReportingFacilityId

def toByte : TradeReportingFacilityId → UInt8
  | .notApplicable => 0x20
  | .inactiveValueA => 0x41
  | .finraNasdaqChicago => 0x42
  | .inactiveValueC => 0x43
  | .inactiveValueD => 0x44
  | .inactiveValueI => 0x49
  | .inactiveValueJ => 0x4A
  | .inactiveValueK => 0x4B
  | .inactiveValueM => 0x4D
  | .finraNyse => 0x4E
  | .inactiveValueP => 0x50
  | .finraNasdaqCarteret => 0x54
  | .inactiveValueV => 0x56
  | .inactiveValueW => 0x57
  | .inactiveValueX => 0x58
  | .inactiveValueY => 0x59
  | .inactiveValueZ => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeReportingFacilityId :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .inactiveValueA
  else if byte = 0x42 then .finraNasdaqChicago
  else if byte = 0x43 then .inactiveValueC
  else if byte = 0x44 then .inactiveValueD
  else if byte = 0x49 then .inactiveValueI
  else if byte = 0x4A then .inactiveValueJ
  else if byte = 0x4B then .inactiveValueK
  else if byte = 0x4D then .inactiveValueM
  else if byte = 0x4E then .finraNyse
  else if byte = 0x50 then .inactiveValueP
  else if byte = 0x54 then .finraNasdaqCarteret
  else if byte = 0x56 then .inactiveValueV
  else if byte = 0x57 then .inactiveValueW
  else if byte = 0x58 then .inactiveValueX
  else if byte = 0x59 then .inactiveValueY
  else .inactiveValueZ

def ofByte (byte : UInt8) : TradeReportingFacilityId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeReportingFacilityId) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | inactiveValueA => decide
  | finraNasdaqChicago => decide
  | inactiveValueC => decide
  | inactiveValueD => decide
  | inactiveValueI => decide
  | inactiveValueJ => decide
  | inactiveValueK => decide
  | inactiveValueM => decide
  | finraNyse => decide
  | inactiveValueP => decide
  | finraNasdaqCarteret => decide
  | inactiveValueV => decide
  | inactiveValueW => decide
  | inactiveValueX => decide
  | inactiveValueY => decide
  | inactiveValueZ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeReportingFacilityId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeReportingFacilityId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeReportingFacilityId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeReportingFacilityId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeReportingFacilityId

/-- Cancel Error Action: one byte code -/
def CancelErrorAction.codes : List UInt8 :=
  [0x31, 0x32]

inductive CancelErrorAction where
  | cancel -- Cancel
  | error -- Error
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelErrorAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelErrorAction

def toByte : CancelErrorAction → UInt8
  | .cancel => 0x31
  | .error => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelErrorAction :=
  if byte = 0x31 then .cancel
  else .error

def ofByte (byte : UInt8) : CancelErrorAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelErrorAction) : ofByte value.toByte = value := by
  cases value with
  | cancel => decide
  | error => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelErrorAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelErrorAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelErrorAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelErrorAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelErrorAction

/-- Primary Listing Market Participant Id: one byte code -/
def PrimaryListingMarketParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryListingMarketParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryListingMarketParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryListingMarketParticipantId

def toByte : PrimaryListingMarketParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryListingMarketParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryListingMarketParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryListingMarketParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryListingMarketParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryListingMarketParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryListingMarketParticipantId

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41]

inductive FinancialStatusIndicator where
  | financialStatusNotApplicable -- Financial Status Not Applicable
  | bankrupt -- Bankrupt
  | belowContinuingListingStandards -- Below Continuing Listing Standards
  | bankruptAndBelowContinuingListingStandards -- Bankrupt And Below Continuing Listing Standards
  | lateFiling -- Late Filing
  | bankruptAndLateFiling -- Bankrupt And Late Filing
  | belowContinuingListingStandardsAndLateFiling -- Below Continuing Listing Standards And Late Filing
  | bankruptBelowContinuingListingStandardsAndLateFiling -- Bankrupt Below Continuing Listing Standards And Late Filing
  | creationsSuspended -- Creations Suspended
  | redemptionsSuspended -- Redemptions Suspended
  | liquidation -- Liquidation
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .financialStatusNotApplicable => 0x30
  | .bankrupt => 0x31
  | .belowContinuingListingStandards => 0x32
  | .bankruptAndBelowContinuingListingStandards => 0x33
  | .lateFiling => 0x34
  | .bankruptAndLateFiling => 0x35
  | .belowContinuingListingStandardsAndLateFiling => 0x36
  | .bankruptBelowContinuingListingStandardsAndLateFiling => 0x37
  | .creationsSuspended => 0x38
  | .redemptionsSuspended => 0x39
  | .liquidation => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x30 then .financialStatusNotApplicable
  else if byte = 0x31 then .bankrupt
  else if byte = 0x32 then .belowContinuingListingStandards
  else if byte = 0x33 then .bankruptAndBelowContinuingListingStandards
  else if byte = 0x34 then .lateFiling
  else if byte = 0x35 then .bankruptAndLateFiling
  else if byte = 0x36 then .belowContinuingListingStandardsAndLateFiling
  else if byte = 0x37 then .bankruptBelowContinuingListingStandardsAndLateFiling
  else if byte = 0x38 then .creationsSuspended
  else if byte = 0x39 then .redemptionsSuspended
  else .liquidation

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | financialStatusNotApplicable => decide
  | bankrupt => decide
  | belowContinuingListingStandards => decide
  | bankruptAndBelowContinuingListingStandards => decide
  | lateFiling => decide
  | bankruptAndLateFiling => decide
  | belowContinuingListingStandardsAndLateFiling => decide
  | bankruptBelowContinuingListingStandardsAndLateFiling => decide
  | creationsSuspended => decide
  | redemptionsSuspended => decide
  | liquidation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialStatusIndicator

/-- Last Participant Id: one byte code -/
def LastParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive LastParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cts -- Cts
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ LastParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastParticipantId

def toByte : LastParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cts => 0x53
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cts
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : LastParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cts => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LastParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastParticipantId

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive Tick where
  | notApplicable -- Not Applicable
  | upward -- Upward
  | downward -- Downward
  | unchangedUpward -- Unchanged Upward
  | unchangedDownward -- Unchanged Downward
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .notApplicable => 0x20
  | .upward => 0x31
  | .downward => 0x32
  | .unchangedUpward => 0x33
  | .unchangedDownward => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x31 then .upward
  else if byte = 0x32 then .downward
  else if byte = 0x33 then .unchangedUpward
  else .unchangedDownward

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | upward => decide
  | downward => decide
  | unchangedUpward => decide
  | unchangedDownward => decide
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

/-- Held Trade Indicator: one byte code -/
def HeldTradeIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive HeldTradeIndicator where
  | notApplicable -- Not Applicable
  | cannotBeUsedAsALastSaleForBothParticipantAndConsolidatedBasis -- Cannot Be Used As A Last Sale For Both Participant And Consolidated Basis
  | canBeUsedAsALastSaleForParticipantButNotConsolidatedBasis -- Can Be Used As A Last Sale For Participant But Not Consolidated Basis
  | canBeUsedAsALastSaleForParticipantAndConsolidatedBasis -- Can Be Used As A Last Sale For Participant And Consolidated Basis
  | unlisted (byte : { byte : UInt8 // byte ∉ HeldTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HeldTradeIndicator

def toByte : HeldTradeIndicator → UInt8
  | .notApplicable => 0x20
  | .cannotBeUsedAsALastSaleForBothParticipantAndConsolidatedBasis => 0x41
  | .canBeUsedAsALastSaleForParticipantButNotConsolidatedBasis => 0x42
  | .canBeUsedAsALastSaleForParticipantAndConsolidatedBasis => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HeldTradeIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .cannotBeUsedAsALastSaleForBothParticipantAndConsolidatedBasis
  else if byte = 0x42 then .canBeUsedAsALastSaleForParticipantButNotConsolidatedBasis
  else .canBeUsedAsALastSaleForParticipantAndConsolidatedBasis

def ofByte (byte : UInt8) : HeldTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HeldTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | cannotBeUsedAsALastSaleForBothParticipantAndConsolidatedBasis => decide
  | canBeUsedAsALastSaleForParticipantButNotConsolidatedBasis => decide
  | canBeUsedAsALastSaleForParticipantAndConsolidatedBasis => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HeldTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HeldTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HeldTradeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HeldTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HeldTradeIndicator

/-- Consolidated High Low Last Indicator: one byte code -/
def ConsolidatedHighLowLastIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48]

inductive ConsolidatedHighLowLastIndicator where
  | none_ -- None
  | high -- High
  | low -- Low
  | last -- Last
  | highLast -- High Last
  | lowLast -- Low Last
  | highLowLast -- High Low Last
  | highLow -- High Low
  | unlisted (byte : { byte : UInt8 // byte ∉ ConsolidatedHighLowLastIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConsolidatedHighLowLastIndicator

def toByte : ConsolidatedHighLowLastIndicator → UInt8
  | .none_ => 0x41
  | .high => 0x42
  | .low => 0x43
  | .last => 0x44
  | .highLast => 0x45
  | .lowLast => 0x46
  | .highLowLast => 0x47
  | .highLow => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ConsolidatedHighLowLastIndicator :=
  if byte = 0x41 then .none_
  else if byte = 0x42 then .high
  else if byte = 0x43 then .low
  else if byte = 0x44 then .last
  else if byte = 0x45 then .highLast
  else if byte = 0x46 then .lowLast
  else if byte = 0x47 then .highLowLast
  else .highLow

def ofByte (byte : UInt8) : ConsolidatedHighLowLastIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConsolidatedHighLowLastIndicator) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | high => decide
  | low => decide
  | last => decide
  | highLast => decide
  | lowLast => decide
  | highLowLast => decide
  | highLow => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ConsolidatedHighLowLastIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConsolidatedHighLowLastIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConsolidatedHighLowLastIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ConsolidatedHighLowLastIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConsolidatedHighLowLastIndicator

/-- Participant Open High Low Last Indicator: one byte code -/
def ParticipantOpenHighLowLastIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51]

inductive ParticipantOpenHighLowLastIndicator where
  | none_ -- None
  | high -- High
  | low -- Low
  | last -- Last
  | highLast -- High Last
  | lowLast -- Low Last
  | unused -- Unused
  | open_ -- Open
  | openHigh -- Open High
  | openLow -- Open Low
  | openHighLowLast -- Open High Low Last
  | openLast -- Open Last
  | openHighLow -- Open High Low
  | openHighLast -- Open High Last
  | openLowLast -- Open Low Last
  | highLow -- High Low
  | highLowLast -- High Low Last
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantOpenHighLowLastIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantOpenHighLowLastIndicator

def toByte : ParticipantOpenHighLowLastIndicator → UInt8
  | .none_ => 0x41
  | .high => 0x42
  | .low => 0x43
  | .last => 0x44
  | .highLast => 0x45
  | .lowLast => 0x46
  | .unused => 0x47
  | .open_ => 0x48
  | .openHigh => 0x49
  | .openLow => 0x4A
  | .openHighLowLast => 0x4B
  | .openLast => 0x4C
  | .openHighLow => 0x4D
  | .openHighLast => 0x4E
  | .openLowLast => 0x4F
  | .highLow => 0x50
  | .highLowLast => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantOpenHighLowLastIndicator :=
  if byte = 0x41 then .none_
  else if byte = 0x42 then .high
  else if byte = 0x43 then .low
  else if byte = 0x44 then .last
  else if byte = 0x45 then .highLast
  else if byte = 0x46 then .lowLast
  else if byte = 0x47 then .unused
  else if byte = 0x48 then .open_
  else if byte = 0x49 then .openHigh
  else if byte = 0x4A then .openLow
  else if byte = 0x4B then .openHighLowLast
  else if byte = 0x4C then .openLast
  else if byte = 0x4D then .openHighLow
  else if byte = 0x4E then .openHighLast
  else if byte = 0x4F then .openLowLast
  else if byte = 0x50 then .highLow
  else .highLowLast

def ofByte (byte : UInt8) : ParticipantOpenHighLowLastIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantOpenHighLowLastIndicator) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | high => decide
  | low => decide
  | last => decide
  | highLast => decide
  | lowLast => decide
  | unused => decide
  | open_ => decide
  | openHigh => decide
  | openLow => decide
  | openHighLowLast => decide
  | openLast => decide
  | openHighLow => decide
  | openHighLast => decide
  | openLowLast => decide
  | highLow => decide
  | highLowLast => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantOpenHighLowLastIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantOpenHighLowLastIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantOpenHighLowLastIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantOpenHighLowLastIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantOpenHighLowLastIndicator

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46]

inductive SecurityStatus where
  | notApplicable -- Not Applicable
  | openingDelay -- Opening Delay
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | noOpenNoResume -- No Open No Resume
  | priceIndication -- Price Indication
  | tradingRangeIndication -- Trading Range Indication
  | marketImbalanceBuy -- Market Imbalance Buy
  | marketImbalanceSell -- Market Imbalance Sell
  | marketOnCloseImbalanceBuy -- Market On Close Imbalance Buy
  | marketOnCloseImbalanceSell -- Market On Close Imbalance Sell
  | reserved -- Reserved
  | noMarketImbalance -- No Market Imbalance
  | noMarketOnCloseImbalance -- No Market On Close Imbalance
  | shortSaleRestriction -- Short Sale Restriction
  | limitUpLimitDown -- Limit Up Limit Down
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .notApplicable => 0x20
  | .openingDelay => 0x31
  | .tradingHalt => 0x32
  | .resume => 0x33
  | .noOpenNoResume => 0x34
  | .priceIndication => 0x35
  | .tradingRangeIndication => 0x36
  | .marketImbalanceBuy => 0x37
  | .marketImbalanceSell => 0x38
  | .marketOnCloseImbalanceBuy => 0x39
  | .marketOnCloseImbalanceSell => 0x41
  | .reserved => 0x42
  | .noMarketImbalance => 0x43
  | .noMarketOnCloseImbalance => 0x44
  | .shortSaleRestriction => 0x45
  | .limitUpLimitDown => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x31 then .openingDelay
  else if byte = 0x32 then .tradingHalt
  else if byte = 0x33 then .resume
  else if byte = 0x34 then .noOpenNoResume
  else if byte = 0x35 then .priceIndication
  else if byte = 0x36 then .tradingRangeIndication
  else if byte = 0x37 then .marketImbalanceBuy
  else if byte = 0x38 then .marketImbalanceSell
  else if byte = 0x39 then .marketOnCloseImbalanceBuy
  else if byte = 0x41 then .marketOnCloseImbalanceSell
  else if byte = 0x42 then .reserved
  else if byte = 0x43 then .noMarketImbalance
  else if byte = 0x44 then .noMarketOnCloseImbalance
  else if byte = 0x45 then .shortSaleRestriction
  else .limitUpLimitDown

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | openingDelay => decide
  | tradingHalt => decide
  | resume => decide
  | noOpenNoResume => decide
  | priceIndication => decide
  | tradingRangeIndication => decide
  | marketImbalanceBuy => decide
  | marketImbalanceSell => decide
  | marketOnCloseImbalanceBuy => decide
  | marketOnCloseImbalanceSell => decide
  | reserved => decide
  | noMarketImbalance => decide
  | noMarketOnCloseImbalance => decide
  | shortSaleRestriction => decide
  | limitUpLimitDown => decide
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

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x20, 0x44, 0x49, 0x4D, 0x50, 0x58, 0x59, 0x31, 0x32, 0x33]

inductive HaltReason where
  | notApplicable -- Not Applicable
  | newsDissemination -- News Dissemination
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownTradingPause -- Limit Up Limit Down Trading Pause
  | newsPending -- News Pending
  | operational -- Operational
  | subpennyTrading -- Subpenny Trading
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .notApplicable => 0x20
  | .newsDissemination => 0x44
  | .orderImbalance => 0x49
  | .limitUpLimitDownTradingPause => 0x4D
  | .newsPending => 0x50
  | .operational => 0x58
  | .subpennyTrading => 0x59
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x44 then .newsDissemination
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownTradingPause
  else if byte = 0x50 then .newsPending
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .subpennyTrading
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else .marketWideCircuitBreakerLevel3Breached

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | newsDissemination => decide
  | orderImbalance => decide
  | limitUpLimitDownTradingPause => decide
  | newsPending => decide
  | operational => decide
  | subpennyTrading => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HaltReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltReason

/-- Limit Up Limit Down Indicator: one byte code -/
def LimitUpLimitDownIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A]

inductive LimitUpLimitDownIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | limitUpLimitDownPriceBand -- Limit Up Limit Down Price Band
  | republishedLimitUpLimitDownPriceBand -- Republished Limit Up Limit Down Price Band
  | nationalBestBidLimitStateEntered -- National Best Bid Limit State Entered
  | nationalBestBidLimitStateExited -- National Best Bid Limit State Exited
  | nationalBestOfferLimitStateEntered -- National Best Offer Limit State Entered
  | nationalBestOfferLimitStateExited -- National Best Offer Limit State Exited
  | nationalBestBidAndNationalBestOfferLimitStateEntered -- National Best Bid And National Best Offer Limit State Entered
  | nationalBestBidAndNationalBestOfferLimitStateExited -- National Best Bid And National Best Offer Limit State Exited
  | nationalBestBidLimitStateEnteredAndNationalBestOfferLimitStateExited -- National Best Bid Limit State Entered And National Best Offer Limit State Exited
  | nationalBestBidLimitStateExitedAndNationalBestOfferLimitStateEntered -- National Best Bid Limit State Exited And National Best Offer Limit State Entered
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitUpLimitDownIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitUpLimitDownIndicator

def toByte : LimitUpLimitDownIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .limitUpLimitDownPriceBand => 0x41
  | .republishedLimitUpLimitDownPriceBand => 0x42
  | .nationalBestBidLimitStateEntered => 0x43
  | .nationalBestBidLimitStateExited => 0x44
  | .nationalBestOfferLimitStateEntered => 0x45
  | .nationalBestOfferLimitStateExited => 0x46
  | .nationalBestBidAndNationalBestOfferLimitStateEntered => 0x47
  | .nationalBestBidAndNationalBestOfferLimitStateExited => 0x48
  | .nationalBestBidLimitStateEnteredAndNationalBestOfferLimitStateExited => 0x49
  | .nationalBestBidLimitStateExitedAndNationalBestOfferLimitStateEntered => 0x4A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitUpLimitDownIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .limitUpLimitDownPriceBand
  else if byte = 0x42 then .republishedLimitUpLimitDownPriceBand
  else if byte = 0x43 then .nationalBestBidLimitStateEntered
  else if byte = 0x44 then .nationalBestBidLimitStateExited
  else if byte = 0x45 then .nationalBestOfferLimitStateEntered
  else if byte = 0x46 then .nationalBestOfferLimitStateExited
  else if byte = 0x47 then .nationalBestBidAndNationalBestOfferLimitStateEntered
  else if byte = 0x48 then .nationalBestBidAndNationalBestOfferLimitStateExited
  else if byte = 0x49 then .nationalBestBidLimitStateEnteredAndNationalBestOfferLimitStateExited
  else .nationalBestBidLimitStateExitedAndNationalBestOfferLimitStateEntered

def ofByte (byte : UInt8) : LimitUpLimitDownIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitUpLimitDownIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | limitUpLimitDownPriceBand => decide
  | republishedLimitUpLimitDownPriceBand => decide
  | nationalBestBidLimitStateEntered => decide
  | nationalBestBidLimitStateExited => decide
  | nationalBestOfferLimitStateEntered => decide
  | nationalBestOfferLimitStateExited => decide
  | nationalBestBidAndNationalBestOfferLimitStateEntered => decide
  | nationalBestBidAndNationalBestOfferLimitStateExited => decide
  | nationalBestBidLimitStateEnteredAndNationalBestOfferLimitStateExited => decide
  | nationalBestBidLimitStateExitedAndNationalBestOfferLimitStateEntered => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitUpLimitDownIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitUpLimitDownIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitUpLimitDownIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LimitUpLimitDownIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitUpLimitDownIndicator

/-- Sale Condition: one byte code -/
def SaleCondition.codes : List UInt8 :=
  [0x20, 0x42, 0x43, 0x45, 0x46, 0x48, 0x49, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x54, 0x55, 0x56, 0x58, 0x5A, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive SaleCondition where
  | regularSale -- Regular Sale
  | averagePriceTrade -- Average Price Trade
  | cashTrade -- Cash Trade
  | automaticExecution -- Automatic Execution
  | intermarketSweepOrder -- Intermarket Sweep Order
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | rule127Or155 -- Rule 127 Or 155
  | soldLast -- Sold Last
  | marketCenterOfficialClose -- Market Center Official Close
  | nextDayTrade -- Next Day Trade
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | priorReferencePrice -- Prior Reference Price
  | marketCenterOfficialOpen -- Market Center Official Open
  | seller -- Seller
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursSold -- Extended Hours Sold
  | contingentTrade -- Contingent Trade
  | crossTrade -- Cross Trade
  | sold -- Sold
  | derivativelyPriced -- Derivatively Priced
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | reserved -- Reserved
  | correctedConsolidatedClosePriceAsPerListingMarket -- Corrected Consolidated Close Price As Per Listing Market
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition

def toByte : SaleCondition → UInt8
  | .regularSale => 0x20
  | .averagePriceTrade => 0x42
  | .cashTrade => 0x43
  | .automaticExecution => 0x45
  | .intermarketSweepOrder => 0x46
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .rule127Or155 => 0x4B
  | .soldLast => 0x4C
  | .marketCenterOfficialClose => 0x4D
  | .nextDayTrade => 0x4E
  | .marketCenterOpeningTrade => 0x4F
  | .priorReferencePrice => 0x50
  | .marketCenterOfficialOpen => 0x51
  | .seller => 0x52
  | .extendedHoursTrade => 0x54
  | .extendedHoursSold => 0x55
  | .contingentTrade => 0x56
  | .crossTrade => 0x58
  | .sold => 0x5A
  | .derivativelyPriced => 0x34
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .qualifiedContingentTrade => 0x37
  | .reserved => 0x38
  | .correctedConsolidatedClosePriceAsPerListingMarket => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition :=
  if byte = 0x20 then .regularSale
  else if byte = 0x42 then .averagePriceTrade
  else if byte = 0x43 then .cashTrade
  else if byte = 0x45 then .automaticExecution
  else if byte = 0x46 then .intermarketSweepOrder
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4B then .rule127Or155
  else if byte = 0x4C then .soldLast
  else if byte = 0x4D then .marketCenterOfficialClose
  else if byte = 0x4E then .nextDayTrade
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .marketCenterOfficialOpen
  else if byte = 0x52 then .seller
  else if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursSold
  else if byte = 0x56 then .contingentTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x5A then .sold
  else if byte = 0x34 then .derivativelyPriced
  else if byte = 0x35 then .marketCenterReopeningTrade
  else if byte = 0x36 then .marketCenterClosingTrade
  else if byte = 0x37 then .qualifiedContingentTrade
  else if byte = 0x38 then .reserved
  else .correctedConsolidatedClosePriceAsPerListingMarket

def ofByte (byte : UInt8) : SaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition) : ofByte value.toByte = value := by
  cases value with
  | regularSale => decide
  | averagePriceTrade => decide
  | cashTrade => decide
  | automaticExecution => decide
  | intermarketSweepOrder => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | rule127Or155 => decide
  | soldLast => decide
  | marketCenterOfficialClose => decide
  | nextDayTrade => decide
  | marketCenterOpeningTrade => decide
  | priorReferencePrice => decide
  | marketCenterOfficialOpen => decide
  | seller => decide
  | extendedHoursTrade => decide
  | extendedHoursSold => decide
  | contingentTrade => decide
  | crossTrade => decide
  | sold => decide
  | derivativelyPriced => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | qualifiedContingentTrade => decide
  | reserved => decide
  | correctedConsolidatedClosePriceAsPerListingMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition

/-- Sale Condition Category: one byte code -/
def SaleConditionCategory.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SaleConditionCategory where
  | notApplicable -- Not Applicable
  | category1 -- Category 1
  | category2 -- Category 2
  | category3 -- Category 3
  | category4 -- Category 4
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionCategory

def toByte : SaleConditionCategory → UInt8
  | .notApplicable => 0x20
  | .category1 => 0x31
  | .category2 => 0x32
  | .category3 => 0x33
  | .category4 => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionCategory :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x31 then .category1
  else if byte = 0x32 then .category2
  else if byte = 0x33 then .category3
  else .category4

def ofByte (byte : UInt8) : SaleConditionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionCategory) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | category1 => decide
  | category2 => decide
  | category3 => decide
  | category4 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionCategory

/-- Sip Block Timestamp: 8 bytes -/
structure SipBlockTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SipBlockTimestamp

def encode (message : SipBlockTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SipBlockTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SipBlockTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SipBlockTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SipBlockTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SipBlockTimestamp

/-- Timestamp 1: 8 bytes -/
structure Timestamp1 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp1

def encode (message : Timestamp1) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp1 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp1) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp1) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp1

/-- Start Of End Of Day Message: 22 bytes -/
structure StartOfEndOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfEndOfDayMessage

def encode (message : StartOfEndOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfEndOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfEndOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfEndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfEndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfEndOfDayMessage

/-- End Of End Of Day Message: 22 bytes -/
structure EndOfEndOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfEndOfDayMessage

def encode (message : EndOfEndOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfEndOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfEndOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfEndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfEndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfEndOfDayMessage

/-- Start Of Start Of Day Message: 22 bytes -/
structure StartOfStartOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfStartOfDayMessage

def encode (message : StartOfStartOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfStartOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfStartOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfStartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfStartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfStartOfDayMessage

/-- End Of Start Of Day Message: 22 bytes -/
structure EndOfStartOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfStartOfDayMessage

def encode (message : EndOfStartOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfStartOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfStartOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfStartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfStartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfStartOfDayMessage

/-- Administrative Unformatted Message: 26 bytes -/
structure AdministrativeUnformattedMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  text : Alpha 4
  deriving DecidableEq, Repr

namespace AdministrativeUnformattedMessage

def encode (message : AdministrativeUnformattedMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.text)))))

def decode (bytes : List UInt8) : Option (AdministrativeUnformattedMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (text, bytes) ← Alpha.decode 4 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, text }, bytes)

@[simp] theorem encode_length (message : AdministrativeUnformattedMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AdministrativeUnformattedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdministrativeUnformattedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AdministrativeUnformattedMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | startOfEndOfDayMessage (message : StartOfEndOfDayMessage) -- "A" 0x41
  | endOfEndOfDayMessage (message : EndOfEndOfDayMessage) -- "B" 0x42
  | startOfStartOfDayMessage (message : StartOfStartOfDayMessage) -- "C" 0x43
  | endOfStartOfDayMessage (message : EndOfStartOfDayMessage) -- "D" 0x44
  | administrativeUnformattedMessage (message : AdministrativeUnformattedMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .startOfEndOfDayMessage _ => 65
  | .endOfEndOfDayMessage _ => 66
  | .startOfStartOfDayMessage _ => 67
  | .endOfStartOfDayMessage _ => 68
  | .administrativeUnformattedMessage _ => 72

def encode : AdministrativeMessagePayload → List UInt8
  | .startOfEndOfDayMessage message => StartOfEndOfDayMessage.encode message
  | .endOfEndOfDayMessage message => EndOfEndOfDayMessage.encode message
  | .startOfStartOfDayMessage message => StartOfStartOfDayMessage.encode message
  | .endOfStartOfDayMessage message => EndOfStartOfDayMessage.encode message
  | .administrativeUnformattedMessage message => AdministrativeUnformattedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 26 := by
  cases message with
  | startOfEndOfDayMessage inner =>
    simp only [encode, StartOfEndOfDayMessage.encode_length]
    omega
  | endOfEndOfDayMessage inner =>
    simp only [encode, EndOfEndOfDayMessage.encode_length]
    omega
  | startOfStartOfDayMessage inner =>
    simp only [encode, StartOfStartOfDayMessage.encode_length]
    omega
  | endOfStartOfDayMessage inner =>
    simp only [encode, EndOfStartOfDayMessage.encode_length]
    omega
  | administrativeUnformattedMessage inner =>
    simp only [encode, AdministrativeUnformattedMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfEndOfDayMessage.decode bytes).map fun (message, rest) => (.startOfEndOfDayMessage message, rest)
  else if tag = 66 then (EndOfEndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfEndOfDayMessage message, rest)
  else if tag = 67 then (StartOfStartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfStartOfDayMessage message, rest)
  else if tag = 68 then (EndOfStartOfDayMessage.decode bytes).map fun (message, rest) => (.endOfStartOfDayMessage message, rest)
  else if tag = 72 then (AdministrativeUnformattedMessage.decode bytes).map fun (message, rest) => (.administrativeUnformattedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Message -/
structure AdministrativeMessage where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 27 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | startOfEndOfDayMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, StartOfEndOfDayMessage.encode_length]
    omega
  | endOfEndOfDayMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, EndOfEndOfDayMessage.encode_length]
    omega
  | startOfStartOfDayMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, StartOfStartOfDayMessage.encode_length]
    omega
  | endOfStartOfDayMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, EndOfStartOfDayMessage.encode_length]
    omega
  | administrativeUnformattedMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, AdministrativeUnformattedMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 22 bytes -/
structure StartOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfDayMessage

/-- Reset Block Sequence Number Message: 22 bytes -/
structure ResetBlockSequenceNumberMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ResetBlockSequenceNumberMessage

def encode (message : ResetBlockSequenceNumberMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (ResetBlockSequenceNumberMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ResetBlockSequenceNumberMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ResetBlockSequenceNumberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetBlockSequenceNumberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResetBlockSequenceNumberMessage

/-- Start Of Test Cycle Message: 22 bytes -/
structure StartOfTestCycleMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfTestCycleMessage

def encode (message : StartOfTestCycleMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfTestCycleMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfTestCycleMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfTestCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfTestCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfTestCycleMessage

/-- End Of Test Cycle Message: 22 bytes -/
structure EndOfTestCycleMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfTestCycleMessage

def encode (message : EndOfTestCycleMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfTestCycleMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfTestCycleMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfTestCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTestCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfTestCycleMessage

/-- Disaster Recovery Data Center Activation Message: 22 bytes -/
structure DisasterRecoveryDataCenterActivationMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace DisasterRecoveryDataCenterActivationMessage

def encode (message : DisasterRecoveryDataCenterActivationMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (DisasterRecoveryDataCenterActivationMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisasterRecoveryDataCenterActivationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisasterRecoveryDataCenterActivationMessage

/-- Line Integrity Message: 22 bytes -/
structure LineIntegrityMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (message : LineIntegrityMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LineIntegrityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LineIntegrityMessage

/-- End Of Day Message: 22 bytes -/
structure EndOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfDayMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "A" 0x41
  | resetBlockSequenceNumberMessage (message : ResetBlockSequenceNumberMessage) -- "L" 0x4C
  | startOfTestCycleMessage (message : StartOfTestCycleMessage) -- "M" 0x4D
  | endOfTestCycleMessage (message : EndOfTestCycleMessage) -- "N" 0x4E
  | disasterRecoveryDataCenterActivationMessage (message : DisasterRecoveryDataCenterActivationMessage) -- "P" 0x50
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | endOfDayMessage (message : EndOfDayMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 65
  | .resetBlockSequenceNumberMessage _ => 76
  | .startOfTestCycleMessage _ => 77
  | .endOfTestCycleMessage _ => 78
  | .disasterRecoveryDataCenterActivationMessage _ => 80
  | .lineIntegrityMessage _ => 84
  | .endOfDayMessage _ => 90

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .resetBlockSequenceNumberMessage message => ResetBlockSequenceNumberMessage.encode message
  | .startOfTestCycleMessage message => StartOfTestCycleMessage.encode message
  | .endOfTestCycleMessage message => EndOfTestCycleMessage.encode message
  | .disasterRecoveryDataCenterActivationMessage message => DisasterRecoveryDataCenterActivationMessage.encode message
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 22 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [encode, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | startOfTestCycleMessage inner =>
    simp only [encode, StartOfTestCycleMessage.encode_length]
    omega
  | endOfTestCycleMessage inner =>
    simp only [encode, EndOfTestCycleMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [encode, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 76 then (ResetBlockSequenceNumberMessage.decode bytes).map fun (message, rest) => (.resetBlockSequenceNumberMessage message, rest)
  else if tag = 77 then (StartOfTestCycleMessage.decode bytes).map fun (message, rest) => (.startOfTestCycleMessage message, rest)
  else if tag = 78 then (EndOfTestCycleMessage.decode bytes).map fun (message, rest) => (.endOfTestCycleMessage message, rest)
  else if tag = 80 then (DisasterRecoveryDataCenterActivationMessage.decode bytes).map fun (message, rest) => (.disasterRecoveryDataCenterActivationMessage message, rest)
  else if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 90 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Message -/
structure ControlMessage where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 23 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | startOfTestCycleMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfTestCycleMessage.encode_length]
    omega
  | endOfTestCycleMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfTestCycleMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Index Message: 41 bytes -/
structure IndexMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  indexSymbol : Alpha 11
  indexValue : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMessage

def encode (message : IndexMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.indexSymbol
    ++ (encodeUInt 8 message.indexValue))))))

def decode (bytes : List UInt8) : Option (IndexMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (indexSymbol, bytes) ← Alpha.decode 11 bytes
  let (indexValue, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, indexSymbol, indexValue }, bytes)

@[simp] theorem encode_length (message : IndexMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMessage

/-- Bid And Offer Index Message: 49 bytes -/
structure BidAndOfferIndexMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  indexSymbol : Alpha 11
  bidIndexValue : BitVec 64
  offerIndexValue : BitVec 64
  deriving DecidableEq, Repr

namespace BidAndOfferIndexMessage

def encode (message : BidAndOfferIndexMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.indexSymbol
    ++ (encodeUInt 8 message.bidIndexValue
    ++ (encodeUInt 8 message.offerIndexValue)))))))

def decode (bytes : List UInt8) : Option (BidAndOfferIndexMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (indexSymbol, bytes) ← Alpha.decode 11 bytes
  let (bidIndexValue, bytes) ← decodeUInt 8 bytes
  let (offerIndexValue, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, indexSymbol, bidIndexValue, offerIndexValue }, bytes)

@[simp] theorem encode_length (message : BidAndOfferIndexMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BidAndOfferIndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidAndOfferIndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidAndOfferIndexMessage

/-- Any Indices Message Payload, selected by Indices Message Type -/
inductive IndicesMessagePayload where
  | indexMessage (message : IndexMessage) -- "I" 0x49
  | bidAndOfferIndexMessage (message : BidAndOfferIndexMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace IndicesMessagePayload

/-- The Indices Message Type each message is sent under -/
def tag : IndicesMessagePayload → BitVec 8
  | .indexMessage _ => 73
  | .bidAndOfferIndexMessage _ => 81

def encode : IndicesMessagePayload → List UInt8
  | .indexMessage message => IndexMessage.encode message
  | .bidAndOfferIndexMessage message => BidAndOfferIndexMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : IndicesMessagePayload) : (encode message).length ≤ 49 := by
  cases message with
  | indexMessage inner =>
    simp only [encode, IndexMessage.encode_length]
    omega
  | bidAndOfferIndexMessage inner =>
    simp only [encode, BidAndOfferIndexMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (IndicesMessagePayload × List UInt8) :=
  if tag = 73 then (IndexMessage.decode bytes).map fun (message, rest) => (.indexMessage message, rest)
  else if tag = 81 then (BidAndOfferIndexMessage.decode bytes).map fun (message, rest) => (.bidAndOfferIndexMessage message, rest)
  else none

@[simp] theorem decode_encode (message : IndicesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end IndicesMessagePayload

/-- Indices Message -/
structure IndicesMessage where
  indicesMessagePayload : IndicesMessagePayload
  deriving DecidableEq, Repr

namespace IndicesMessage

def encode (message : IndicesMessage) : List UInt8 :=
  encodeUInt 1 (IndicesMessagePayload.tag message.indicesMessagePayload)
    ++ (IndicesMessagePayload.encode message.indicesMessagePayload)

def decode (bytes : List UInt8) : Option (IndicesMessage × List UInt8) := do
  let (indicesMessageType, bytes) ← decodeUInt 1 bytes
  let (indicesMessagePayload, bytes) ← IndicesMessagePayload.decode indicesMessageType bytes
  pure ({ indicesMessagePayload }, bytes)

theorem encode_length_pos (message : IndicesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndicesMessage) : (encode message).length ≤ 50 := by
  unfold encode
  cases message.indicesMessagePayload with
  | indexMessage inner =>
    simp only [IndicesMessagePayload.encode, List.length_append, encodeUInt_length, IndexMessage.encode_length]
    omega
  | bidAndOfferIndexMessage inner =>
    simp only [IndicesMessagePayload.encode, List.length_append, encodeUInt_length, BidAndOfferIndexMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : IndicesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [IndicesMessagePayload.decode_encode, some_bind]
  rfl

end IndicesMessage

/-- Market Wide Circuit Breaker Decline Level Status Message: 47 bytes -/
structure MarketWideCircuitBreakerDeclineLevelStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  reserved : BitVec 8
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelStatusMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3
    ++ (encodeUInt 1 message.reserved))))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, mwcbLevel1, mwcbLevel2, mwcbLevel3, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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

end MarketWideCircuitBreakerDeclineLevelStatusMessage

/-- Market Wide Circuit Breaker Status Message: 24 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  marketWideCircuitBreakerLevelIndicator : MarketWideCircuitBreakerLevelIndicator
  reserved : BitVec 8
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (MarketWideCircuitBreakerLevelIndicator.encode message.marketWideCircuitBreakerLevelIndicator
    ++ (encodeUInt 1 message.reserved))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketWideCircuitBreakerLevelIndicator, bytes) ← MarketWideCircuitBreakerLevelIndicator.decode bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, marketWideCircuitBreakerLevelIndicator, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, MarketWideCircuitBreakerLevelIndicator.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketWideCircuitBreakerLevelIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Participants: 9 bytes -/
structure Participants where
  participantId : ParticipantId
  tradeTotalVolume : BitVec 64
  deriving DecidableEq, Repr

namespace Participants

def encode (message : Participants) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (encodeUInt 8 message.tradeTotalVolume)

def decode (bytes : List UInt8) : Option (Participants × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (tradeTotalVolume, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, tradeTotalVolume }, bytes)

@[simp] theorem encode_length (message : Participants) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, encodeUInt_length]

theorem encode_length_pos (message : Participants) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Participants) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Participants

/-- Approximate Adjusted Volume Market Center Message -/
structure ApproximateAdjustedVolumeMarketCenterMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  participants : Bounded 1 Participants
  deriving DecidableEq, Repr

namespace ApproximateAdjustedVolumeMarketCenterMessage

def encode (message : ApproximateAdjustedVolumeMarketCenterMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.participants.val.length)
    ++ (encodeMany Participants.encode message.participants.val))))))

def decode (bytes : List UInt8) : Option (ApproximateAdjustedVolumeMarketCenterMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (numberOfParticipants, bytes) ← decodeUInt 1 bytes
  let (participants_, bytes) ← decodeMany Participants.decode numberOfParticipants.toNat bytes
  if fits_participants : participants_.length < 256 ^ 1 then
    pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, participants := ⟨participants_, fits_participants⟩ }, bytes)
  else none

theorem encode_length_pos (message : ApproximateAdjustedVolumeMarketCenterMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApproximateAdjustedVolumeMarketCenterMessage) : (encode message).length ≤ 2318 := by
  have bound_participants := message.participants.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, encodeMany_length_const Participants.encode 9 Participants.encode_length]
  omega

@[simp] theorem decode_encode (message : ApproximateAdjustedVolumeMarketCenterMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Participants.encode Participants.decode Participants.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.participants.length_lt]
  rfl

end ApproximateAdjustedVolumeMarketCenterMessage

/-- Approximate Trades And Total Dollar Value Message: 34 bytes -/
structure ApproximateTradesAndTotalDollarValueMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  totalTrades : BitVec 32
  dollarValue : BitVec 64
  deriving DecidableEq, Repr

namespace ApproximateTradesAndTotalDollarValueMessage

def encode (message : ApproximateTradesAndTotalDollarValueMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 4 message.totalTrades
    ++ (encodeUInt 8 message.dollarValue))))))

def decode (bytes : List UInt8) : Option (ApproximateTradesAndTotalDollarValueMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (totalTrades, bytes) ← decodeUInt 4 bytes
  let (dollarValue, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, totalTrades, dollarValue }, bytes)

@[simp] theorem encode_length (message : ApproximateTradesAndTotalDollarValueMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ApproximateTradesAndTotalDollarValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApproximateTradesAndTotalDollarValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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

end ApproximateTradesAndTotalDollarValueMessage

/-- Crossing Session Summary Message: 46 bytes -/
structure CrossingSessionSummaryMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  crossingSession1TotalTradesVolume : BitVec 64
  crossingSession2DollarValue : BitVec 64
  crossingSession2TotalTradesVolume : BitVec 64
  deriving DecidableEq, Repr

namespace CrossingSessionSummaryMessage

def encode (message : CrossingSessionSummaryMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 8 message.crossingSession1TotalTradesVolume
    ++ (encodeUInt 8 message.crossingSession2DollarValue
    ++ (encodeUInt 8 message.crossingSession2TotalTradesVolume)))))))

def decode (bytes : List UInt8) : Option (CrossingSessionSummaryMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (crossingSession1TotalTradesVolume, bytes) ← decodeUInt 8 bytes
  let (crossingSession2DollarValue, bytes) ← decodeUInt 8 bytes
  let (crossingSession2TotalTradesVolume, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, crossingSession1TotalTradesVolume, crossingSession2DollarValue, crossingSession2TotalTradesVolume }, bytes)

@[simp] theorem encode_length (message : CrossingSessionSummaryMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CrossingSessionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossingSessionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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

end CrossingSessionSummaryMessage

/-- Any Market Status Message Payload, selected by Market Status Message Type -/
inductive MarketStatusMessagePayload where
  | marketWideCircuitBreakerDeclineLevelStatusMessage (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) -- "M" 0x4D
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- "L" 0x4C
  | approximateAdjustedVolumeMarketCenterMessage (message : ApproximateAdjustedVolumeMarketCenterMessage) -- "N" 0x4E
  | approximateTradesAndTotalDollarValueMessage (message : ApproximateTradesAndTotalDollarValueMessage) -- "O" 0x4F
  | crossingSessionSummaryMessage (message : CrossingSessionSummaryMessage) -- "P" 0x50
  deriving DecidableEq, Repr

namespace MarketStatusMessagePayload

/-- The Market Status Message Type each message is sent under -/
def tag : MarketStatusMessagePayload → BitVec 8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage _ => 77
  | .marketWideCircuitBreakerStatusMessage _ => 76
  | .approximateAdjustedVolumeMarketCenterMessage _ => 78
  | .approximateTradesAndTotalDollarValueMessage _ => 79
  | .crossingSessionSummaryMessage _ => 80

def encode : MarketStatusMessagePayload → List UInt8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage message => MarketWideCircuitBreakerDeclineLevelStatusMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message
  | .approximateAdjustedVolumeMarketCenterMessage message => ApproximateAdjustedVolumeMarketCenterMessage.encode message
  | .approximateTradesAndTotalDollarValueMessage message => ApproximateTradesAndTotalDollarValueMessage.encode message
  | .crossingSessionSummaryMessage message => CrossingSessionSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MarketStatusMessagePayload) : (encode message).length ≤ 2318 := by
  cases message with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | approximateAdjustedVolumeMarketCenterMessage inner =>
    have bound_inner := ApproximateAdjustedVolumeMarketCenterMessage.encode_length_le inner
    simp only [encode]
    omega
  | approximateTradesAndTotalDollarValueMessage inner =>
    simp only [encode, ApproximateTradesAndTotalDollarValueMessage.encode_length]
    omega
  | crossingSessionSummaryMessage inner =>
    simp only [encode, CrossingSessionSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MarketStatusMessagePayload × List UInt8) :=
  if tag = 77 then (MarketWideCircuitBreakerDeclineLevelStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelStatusMessage message, rest)
  else if tag = 76 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
  else if tag = 78 then (ApproximateAdjustedVolumeMarketCenterMessage.decode bytes).map fun (message, rest) => (.approximateAdjustedVolumeMarketCenterMessage message, rest)
  else if tag = 79 then (ApproximateTradesAndTotalDollarValueMessage.decode bytes).map fun (message, rest) => (.approximateTradesAndTotalDollarValueMessage message, rest)
  else if tag = 80 then (CrossingSessionSummaryMessage.decode bytes).map fun (message, rest) => (.crossingSessionSummaryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MarketStatusMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MarketStatusMessagePayload

/-- Market Status Message -/
structure MarketStatusMessage where
  marketStatusMessagePayload : MarketStatusMessagePayload
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUInt 1 (MarketStatusMessagePayload.tag message.marketStatusMessagePayload)
    ++ (MarketStatusMessagePayload.encode message.marketStatusMessagePayload)

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (marketStatusMessageType, bytes) ← decodeUInt 1 bytes
  let (marketStatusMessagePayload, bytes) ← MarketStatusMessagePayload.decode marketStatusMessageType bytes
  pure ({ marketStatusMessagePayload }, bytes)

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatusMessage) : (encode message).length ≤ 2319 := by
  unfold encode
  cases message.marketStatusMessagePayload with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | approximateAdjustedVolumeMarketCenterMessage inner =>
    have bound_inner := ApproximateAdjustedVolumeMarketCenterMessage.encode_length_le inner
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | approximateTradesAndTotalDollarValueMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, ApproximateTradesAndTotalDollarValueMessage.encode_length]
    omega
  | crossingSessionSummaryMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, CrossingSessionSummaryMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MarketStatusMessagePayload.decode_encode, some_bind]
  rfl

end MarketStatusMessage

/-- Sale Conditions: 4 bytes -/
structure SaleConditions where
  category1 : Alpha 1
  category2 : Category2
  category3 : Category3
  category4 : Category4
  deriving DecidableEq, Repr

namespace SaleConditions

def encode (message : SaleConditions) : List UInt8 :=
  Alpha.encode message.category1
    ++ (Category2.encode message.category2
    ++ (Category3.encode message.category3
    ++ (Category4.encode message.category4)))

def decode (bytes : List UInt8) : Option (SaleConditions × List UInt8) := do
  let (category1, bytes) ← Alpha.decode 1 bytes
  let (category2, bytes) ← Category2.decode bytes
  let (category3, bytes) ← Category3.decode bytes
  let (category4, bytes) ← Category4.decode bytes
  pure ({ category1, category2, category3, category4 }, bytes)

@[simp] theorem encode_length (message : SaleConditions) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Category2.encode_length, Category3.encode_length, Category4.encode_length]

theorem encode_length_pos (message : SaleConditions) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SaleConditions) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Category2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Category3.decode_encode, some_bind]
  dsimp only
  rw [Category4.decode_encode, some_bind]
  rfl

end SaleConditions

/-- Prior Day Trade Date And Time: 8 bytes -/
structure PriorDayTradeDateAndTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace PriorDayTradeDateAndTime

def encode (message : PriorDayTradeDateAndTime) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (PriorDayTradeDateAndTime × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeDateAndTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriorDayTradeDateAndTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeDateAndTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriorDayTradeDateAndTime

/-- Corrected Trade: 28 bytes -/
structure CorrectedTrade where
  saleConditions : SaleConditions
  tradePriceLong : BitVec 64
  tradeVolumeLong : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace CorrectedTrade

def encode (message : CorrectedTrade) : List UInt8 :=
  SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePriceLong
    ++ (encodeUInt 4 message.tradeVolumeLong
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime)))))))

def decode (bytes : List UInt8) : Option (CorrectedTrade × List UInt8) := do
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePriceLong, bytes) ← decodeUInt 8 bytes
  let (tradeVolumeLong, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  pure ({ saleConditions, tradePriceLong, tradeVolumeLong, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, priorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : CorrectedTrade) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, SaleConditions.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, PriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : CorrectedTrade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedTrade) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [PriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end CorrectedTrade

/-- Original Trade: 28 bytes -/
structure OriginalTrade where
  saleConditions : SaleConditions
  tradePriceLong : BitVec 64
  tradeVolumeLong : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace OriginalTrade

def encode (message : OriginalTrade) : List UInt8 :=
  SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePriceLong
    ++ (encodeUInt 4 message.tradeVolumeLong
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime)))))))

def decode (bytes : List UInt8) : Option (OriginalTrade × List UInt8) := do
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePriceLong, bytes) ← decodeUInt 8 bytes
  let (tradeVolumeLong, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  pure ({ saleConditions, tradePriceLong, tradeVolumeLong, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, priorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : OriginalTrade) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, SaleConditions.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, PriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : OriginalTrade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalTrade) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [PriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end OriginalTrade

/-- Prior Day Trade Correction Message: 91 bytes -/
structure PriorDayTradeCorrectionMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedTrade : CorrectedTrade
  tradeReportingFacilityId : TradeReportingFacilityId
  originalTrade : OriginalTrade
  deriving DecidableEq, Repr

namespace PriorDayTradeCorrectionMessage

def encode (message : PriorDayTradeCorrectionMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (CorrectedTrade.encode message.correctedTrade
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (OriginalTrade.encode message.originalTrade)))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeCorrectionMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedTrade, bytes) ← CorrectedTrade.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (originalTrade, bytes) ← OriginalTrade.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, correctedTrade, tradeReportingFacilityId, originalTrade }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeCorrectionMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, CorrectedTrade.encode_length, TradeReportingFacilityId.encode_length, OriginalTrade.encode_length]

theorem encode_length_pos (message : PriorDayTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [OriginalTrade.decode_encode, some_bind]
  rfl

end PriorDayTradeCorrectionMessage

/-- Prior Day Trade Message: 63 bytes -/
structure PriorDayTradeMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleConditions : SaleConditions
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace PriorDayTradeMessage

def encode (message : PriorDayTradeMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime)))))))))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, saleConditions, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, SaleConditions.encode_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : PriorDayTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [PriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end PriorDayTradeMessage

/-- Prior Day Trade Cancel Error Message: 64 bytes -/
structure PriorDayTradeCancelErrorMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleConditions : SaleConditions
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  cancelErrorAction : CancelErrorAction
  deriving DecidableEq, Repr

namespace PriorDayTradeCancelErrorMessage

def encode (message : PriorDayTradeCancelErrorMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime
    ++ (CancelErrorAction.encode message.cancelErrorAction))))))))))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeCancelErrorMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  let (cancelErrorAction, bytes) ← CancelErrorAction.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, saleConditions, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime, cancelErrorAction }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeCancelErrorMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, SaleConditions.encode_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length, CancelErrorAction.encode_length]

theorem encode_length_pos (message : PriorDayTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriorDayTradeDateAndTime.decode_encode, some_bind]
  dsimp only
  rw [CancelErrorAction.decode_encode, some_bind]
  rfl

end PriorDayTradeCancelErrorMessage

/-- Any Prior Day Message Payload, selected by Prior Day Message Type -/
inductive PriorDayMessagePayload where
  | priorDayTradeCorrectionMessage (message : PriorDayTradeCorrectionMessage) -- "C" 0x43
  | priorDayTradeMessage (message : PriorDayTradeMessage) -- "T" 0x54
  | priorDayTradeCancelErrorMessage (message : PriorDayTradeCancelErrorMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace PriorDayMessagePayload

/-- The Prior Day Message Type each message is sent under -/
def tag : PriorDayMessagePayload → BitVec 8
  | .priorDayTradeCorrectionMessage _ => 67
  | .priorDayTradeMessage _ => 84
  | .priorDayTradeCancelErrorMessage _ => 88

def encode : PriorDayMessagePayload → List UInt8
  | .priorDayTradeCorrectionMessage message => PriorDayTradeCorrectionMessage.encode message
  | .priorDayTradeMessage message => PriorDayTradeMessage.encode message
  | .priorDayTradeCancelErrorMessage message => PriorDayTradeCancelErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : PriorDayMessagePayload) : (encode message).length ≤ 91 := by
  cases message with
  | priorDayTradeCorrectionMessage inner =>
    simp only [encode, PriorDayTradeCorrectionMessage.encode_length]
    omega
  | priorDayTradeMessage inner =>
    simp only [encode, PriorDayTradeMessage.encode_length]
    omega
  | priorDayTradeCancelErrorMessage inner =>
    simp only [encode, PriorDayTradeCancelErrorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (PriorDayMessagePayload × List UInt8) :=
  if tag = 67 then (PriorDayTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.priorDayTradeCorrectionMessage message, rest)
  else if tag = 84 then (PriorDayTradeMessage.decode bytes).map fun (message, rest) => (.priorDayTradeMessage message, rest)
  else if tag = 88 then (PriorDayTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.priorDayTradeCancelErrorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : PriorDayMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end PriorDayMessagePayload

/-- Prior Day Message -/
structure PriorDayMessage where
  priorDayMessagePayload : PriorDayMessagePayload
  deriving DecidableEq, Repr

namespace PriorDayMessage

def encode (message : PriorDayMessage) : List UInt8 :=
  encodeUInt 1 (PriorDayMessagePayload.tag message.priorDayMessagePayload)
    ++ (PriorDayMessagePayload.encode message.priorDayMessagePayload)

def decode (bytes : List UInt8) : Option (PriorDayMessage × List UInt8) := do
  let (priorDayMessageType, bytes) ← decodeUInt 1 bytes
  let (priorDayMessagePayload, bytes) ← PriorDayMessagePayload.decode priorDayMessageType bytes
  pure ({ priorDayMessagePayload }, bytes)

theorem encode_length_pos (message : PriorDayMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriorDayMessage) : (encode message).length ≤ 92 := by
  unfold encode
  cases message.priorDayMessagePayload with
  | priorDayTradeCorrectionMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeCorrectionMessage.encode_length]
    omega
  | priorDayTradeMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeMessage.encode_length]
    omega
  | priorDayTradeCancelErrorMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeCancelErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : PriorDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PriorDayMessagePayload.decode_encode, some_bind]
  rfl

end PriorDayMessage

/-- Consolidated Start Of Day Summary Message: 51 bytes -/
structure ConsolidatedStartOfDaySummaryMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  summaryParticipantId : Alpha 1
  previousClosePriceDate : BitVec 32
  previousClosePrice : BitVec 64
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  numberOfParticipants : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedStartOfDaySummaryMessage

def encode (message : ConsolidatedStartOfDaySummaryMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.summaryParticipantId
    ++ (encodeUInt 4 message.previousClosePriceDate
    ++ (encodeUInt 8 message.previousClosePrice
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 1 message.numberOfParticipants)))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedStartOfDaySummaryMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (summaryParticipantId, bytes) ← Alpha.decode 1 bytes
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (previousClosePrice, bytes) ← decodeUInt 8 bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (numberOfParticipants, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, summaryParticipantId, previousClosePriceDate, previousClosePrice, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, numberOfParticipants }, bytes)

@[simp] theorem encode_length (message : ConsolidatedStartOfDaySummaryMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : ConsolidatedStartOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedStartOfDaySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedStartOfDaySummaryMessage

/-- Participant Start Of Day Summary Message: 47 bytes -/
structure ParticipantStartOfDaySummaryMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  summaryParticipantId : Alpha 1
  previousClosePriceDate : BitVec 32
  previousClosePrice : BitVec 64
  deriving DecidableEq, Repr

namespace ParticipantStartOfDaySummaryMessage

def encode (message : ParticipantStartOfDaySummaryMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.summaryParticipantId
    ++ (encodeUInt 4 message.previousClosePriceDate
    ++ (encodeUInt 8 message.previousClosePrice)))))))))

def decode (bytes : List UInt8) : Option (ParticipantStartOfDaySummaryMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (summaryParticipantId, bytes) ← Alpha.decode 1 bytes
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (previousClosePrice, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, summaryParticipantId, previousClosePriceDate, previousClosePrice }, bytes)

@[simp] theorem encode_length (message : ParticipantStartOfDaySummaryMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : ParticipantStartOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantStartOfDaySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ParticipantStartOfDaySummaryMessage

/-- Consolidated End Of Day Summary Message: 75 bytes -/
structure ConsolidatedEndOfDaySummaryMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  lastParticipantId : LastParticipantId
  previousClosePriceDate : BitVec 32
  lastPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  totalVolume : BitVec 64
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  numberOfParticipants : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedEndOfDaySummaryMessage

def encode (message : ConsolidatedEndOfDaySummaryMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (LastParticipantId.encode message.lastParticipantId
    ++ (encodeUInt 4 message.previousClosePriceDate
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.highPrice
    ++ (encodeUInt 8 message.lowPrice
    ++ (encodeUInt 8 message.totalVolume
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 1 message.numberOfParticipants))))))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedEndOfDaySummaryMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (lastParticipantId, bytes) ← LastParticipantId.decode bytes
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (highPrice, bytes) ← decodeUInt 8 bytes
  let (lowPrice, bytes) ← decodeUInt 8 bytes
  let (totalVolume, bytes) ← decodeUInt 8 bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (numberOfParticipants, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, lastParticipantId, previousClosePriceDate, lastPrice, highPrice, lowPrice, totalVolume, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, numberOfParticipants }, bytes)

@[simp] theorem encode_length (message : ConsolidatedEndOfDaySummaryMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, LastParticipantId.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : ConsolidatedEndOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedEndOfDaySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastParticipantId.decode_encode, some_bind]
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
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedEndOfDaySummaryMessage

/-- Participant End Of Day Summary Message: 80 bytes -/
structure ParticipantEndOfDaySummaryMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  summaryParticipantId : Alpha 1
  previousClosePriceDate : BitVec 32
  lastPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  openPrice : BitVec 64
  totalVolume : BitVec 64
  tick : Tick
  deriving DecidableEq, Repr

namespace ParticipantEndOfDaySummaryMessage

def encode (message : ParticipantEndOfDaySummaryMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.summaryParticipantId
    ++ (encodeUInt 4 message.previousClosePriceDate
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.highPrice
    ++ (encodeUInt 8 message.lowPrice
    ++ (encodeUInt 8 message.openPrice
    ++ (encodeUInt 8 message.totalVolume
    ++ (Tick.encode message.tick))))))))))))))

def decode (bytes : List UInt8) : Option (ParticipantEndOfDaySummaryMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (summaryParticipantId, bytes) ← Alpha.decode 1 bytes
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (highPrice, bytes) ← decodeUInt 8 bytes
  let (lowPrice, bytes) ← decodeUInt 8 bytes
  let (openPrice, bytes) ← decodeUInt 8 bytes
  let (totalVolume, bytes) ← decodeUInt 8 bytes
  let (tick, bytes) ← Tick.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, summaryParticipantId, previousClosePriceDate, lastPrice, highPrice, lowPrice, openPrice, totalVolume, tick }, bytes)

@[simp] theorem encode_length (message : ParticipantEndOfDaySummaryMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, Tick.encode_length]

theorem encode_length_pos (message : ParticipantEndOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantEndOfDaySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Tick.decode_encode, some_bind]
  rfl

end ParticipantEndOfDaySummaryMessage

/-- Any Summary Message Payload, selected by Summary Message Type -/
inductive SummaryMessagePayload where
  | consolidatedStartOfDaySummaryMessage (message : ConsolidatedStartOfDaySummaryMessage) -- "A" 0x41
  | participantStartOfDaySummaryMessage (message : ParticipantStartOfDaySummaryMessage) -- "B" 0x42
  | consolidatedEndOfDaySummaryMessage (message : ConsolidatedEndOfDaySummaryMessage) -- "C" 0x43
  | participantEndOfDaySummaryMessage (message : ParticipantEndOfDaySummaryMessage) -- "D" 0x44
  deriving DecidableEq, Repr

namespace SummaryMessagePayload

/-- The Summary Message Type each message is sent under -/
def tag : SummaryMessagePayload → BitVec 8
  | .consolidatedStartOfDaySummaryMessage _ => 65
  | .participantStartOfDaySummaryMessage _ => 66
  | .consolidatedEndOfDaySummaryMessage _ => 67
  | .participantEndOfDaySummaryMessage _ => 68

def encode : SummaryMessagePayload → List UInt8
  | .consolidatedStartOfDaySummaryMessage message => ConsolidatedStartOfDaySummaryMessage.encode message
  | .participantStartOfDaySummaryMessage message => ParticipantStartOfDaySummaryMessage.encode message
  | .consolidatedEndOfDaySummaryMessage message => ConsolidatedEndOfDaySummaryMessage.encode message
  | .participantEndOfDaySummaryMessage message => ParticipantEndOfDaySummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SummaryMessagePayload) : (encode message).length ≤ 80 := by
  cases message with
  | consolidatedStartOfDaySummaryMessage inner =>
    simp only [encode, ConsolidatedStartOfDaySummaryMessage.encode_length]
    omega
  | participantStartOfDaySummaryMessage inner =>
    simp only [encode, ParticipantStartOfDaySummaryMessage.encode_length]
    omega
  | consolidatedEndOfDaySummaryMessage inner =>
    simp only [encode, ConsolidatedEndOfDaySummaryMessage.encode_length]
    omega
  | participantEndOfDaySummaryMessage inner =>
    simp only [encode, ParticipantEndOfDaySummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SummaryMessagePayload × List UInt8) :=
  if tag = 65 then (ConsolidatedStartOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.consolidatedStartOfDaySummaryMessage message, rest)
  else if tag = 66 then (ParticipantStartOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.participantStartOfDaySummaryMessage message, rest)
  else if tag = 67 then (ConsolidatedEndOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.consolidatedEndOfDaySummaryMessage message, rest)
  else if tag = 68 then (ParticipantEndOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.participantEndOfDaySummaryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SummaryMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SummaryMessagePayload

/-- Summary Message -/
structure SummaryMessage where
  summaryMessagePayload : SummaryMessagePayload
  deriving DecidableEq, Repr

namespace SummaryMessage

def encode (message : SummaryMessage) : List UInt8 :=
  encodeUInt 1 (SummaryMessagePayload.tag message.summaryMessagePayload)
    ++ (SummaryMessagePayload.encode message.summaryMessagePayload)

def decode (bytes : List UInt8) : Option (SummaryMessage × List UInt8) := do
  let (summaryMessageType, bytes) ← decodeUInt 1 bytes
  let (summaryMessagePayload, bytes) ← SummaryMessagePayload.decode summaryMessageType bytes
  pure ({ summaryMessagePayload }, bytes)

theorem encode_length_pos (message : SummaryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SummaryMessage) : (encode message).length ≤ 81 := by
  unfold encode
  cases message.summaryMessagePayload with
  | consolidatedStartOfDaySummaryMessage inner =>
    simp only [SummaryMessagePayload.encode, List.length_append, encodeUInt_length, ConsolidatedStartOfDaySummaryMessage.encode_length]
    omega
  | participantStartOfDaySummaryMessage inner =>
    simp only [SummaryMessagePayload.encode, List.length_append, encodeUInt_length, ParticipantStartOfDaySummaryMessage.encode_length]
    omega
  | consolidatedEndOfDaySummaryMessage inner =>
    simp only [SummaryMessagePayload.encode, List.length_append, encodeUInt_length, ConsolidatedEndOfDaySummaryMessage.encode_length]
    omega
  | participantEndOfDaySummaryMessage inner =>
    simp only [SummaryMessagePayload.encode, List.length_append, encodeUInt_length, ParticipantEndOfDaySummaryMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SummaryMessagePayload.decode_encode, some_bind]
  rfl

end SummaryMessage

/-- Auction Status Message: 124 bytes -/
structure AuctionStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  futureUse : Alpha 62
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (Alpha.encode message.futureUse))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (futureUse, bytes) ← Alpha.decode 62 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, futureUse }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionStatusMessage

/-- Timestamp 2: 8 bytes -/
structure Timestamp2 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp2

def encode (message : Timestamp2) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp2 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp2) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp2

/-- Consolidated Data: 38 bytes -/
structure ConsolidatedData where
  previousClosePriceDate : BitVec 32
  lastParticipantId : LastParticipantId
  lastPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  totalVolume : BitVec 64
  tick : Tick
  deriving DecidableEq, Repr

namespace ConsolidatedData

def encode (message : ConsolidatedData) : List UInt8 :=
  encodeUInt 4 message.previousClosePriceDate
    ++ (LastParticipantId.encode message.lastParticipantId
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.highPrice
    ++ (encodeUInt 8 message.lowPrice
    ++ (encodeUInt 8 message.totalVolume
    ++ (Tick.encode message.tick))))))

def decode (bytes : List UInt8) : Option (ConsolidatedData × List UInt8) := do
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (lastParticipantId, bytes) ← LastParticipantId.decode bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (highPrice, bytes) ← decodeUInt 8 bytes
  let (lowPrice, bytes) ← decodeUInt 8 bytes
  let (totalVolume, bytes) ← decodeUInt 8 bytes
  let (tick, bytes) ← Tick.decode bytes
  pure ({ previousClosePriceDate, lastParticipantId, lastPrice, highPrice, lowPrice, totalVolume, tick }, bytes)

@[simp] theorem encode_length (message : ConsolidatedData) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LastParticipantId.encode_length, Tick.encode_length]

theorem encode_length_pos (message : ConsolidatedData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LastParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Tick.decode_encode, some_bind]
  rfl

end ConsolidatedData

/-- Participant Data: 38 bytes -/
structure ParticipantData where
  previousClosePriceDate : BitVec 32
  lastParticipantId : LastParticipantId
  lastPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  totalVolume : BitVec 64
  tick : Tick
  deriving DecidableEq, Repr

namespace ParticipantData

def encode (message : ParticipantData) : List UInt8 :=
  encodeUInt 4 message.previousClosePriceDate
    ++ (LastParticipantId.encode message.lastParticipantId
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.highPrice
    ++ (encodeUInt 8 message.lowPrice
    ++ (encodeUInt 8 message.totalVolume
    ++ (Tick.encode message.tick))))))

def decode (bytes : List UInt8) : Option (ParticipantData × List UInt8) := do
  let (previousClosePriceDate, bytes) ← decodeUInt 4 bytes
  let (lastParticipantId, bytes) ← LastParticipantId.decode bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (highPrice, bytes) ← decodeUInt 8 bytes
  let (lowPrice, bytes) ← decodeUInt 8 bytes
  let (totalVolume, bytes) ← decodeUInt 8 bytes
  let (tick, bytes) ← Tick.decode bytes
  pure ({ previousClosePriceDate, lastParticipantId, lastPrice, highPrice, lowPrice, totalVolume, tick }, bytes)

@[simp] theorem encode_length (message : ParticipantData) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LastParticipantId.encode_length, Tick.encode_length]

theorem encode_length_pos (message : ParticipantData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LastParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Tick.decode_encode, some_bind]
  rfl

end ParticipantData

/-- Trade Correction Message: 185 bytes -/
structure TradeCorrectionMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedTrade : CorrectedTrade
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  originalParticipantReferenceNumber : BitVec 64
  originalTrade : OriginalTrade
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  consolidatedData : ConsolidatedData
  participantData : ParticipantData
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (CorrectedTrade.encode message.correctedTrade
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2
    ++ (encodeUInt 8 message.originalParticipantReferenceNumber
    ++ (OriginalTrade.encode message.originalTrade
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ConsolidatedData.encode message.consolidatedData
    ++ (ParticipantData.encode message.participantData)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedTrade, bytes) ← CorrectedTrade.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (originalParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (originalTrade, bytes) ← OriginalTrade.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (consolidatedData, bytes) ← ConsolidatedData.decode bytes
  let (participantData, bytes) ← ParticipantData.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, correctedTrade, tradeReportingFacilityId, timestamp2, originalParticipantReferenceNumber, originalTrade, primaryListingMarketParticipantId, financialStatusIndicator, consolidatedData, participantData }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 185 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, CorrectedTrade.encode_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length, OriginalTrade.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, ConsolidatedData.encode_length, ParticipantData.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedData.decode_encode, some_bind]
  dsimp only
  rw [ParticipantData.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Long Trade Message: 68 bytes -/
structure LongTradeMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleConditions : SaleConditions
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  heldTradeIndicator : HeldTradeIndicator
  consolidatedHighLowLastIndicator : ConsolidatedHighLowLastIndicator
  participantOpenHighLowLastIndicator : ParticipantOpenHighLowLastIndicator
  deriving DecidableEq, Repr

namespace LongTradeMessage

def encode (message : LongTradeMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (HeldTradeIndicator.encode message.heldTradeIndicator
    ++ (ConsolidatedHighLowLastIndicator.encode message.consolidatedHighLowLastIndicator
    ++ (ParticipantOpenHighLowLastIndicator.encode message.participantOpenHighLowLastIndicator))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LongTradeMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (heldTradeIndicator, bytes) ← HeldTradeIndicator.decode bytes
  let (consolidatedHighLowLastIndicator, bytes) ← ConsolidatedHighLowLastIndicator.decode bytes
  let (participantOpenHighLowLastIndicator, bytes) ← ParticipantOpenHighLowLastIndicator.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, saleConditions, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, tradeReportingFacilityId, timestamp2, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, heldTradeIndicator, consolidatedHighLowLastIndicator, participantOpenHighLowLastIndicator }, bytes)

@[simp] theorem encode_length (message : LongTradeMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, SaleConditions.encode_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, HeldTradeIndicator.encode_length, ConsolidatedHighLowLastIndicator.encode_length, ParticipantOpenHighLowLastIndicator.encode_length]

theorem encode_length_pos (message : LongTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HeldTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedHighLowLastIndicator.decode_encode, some_bind]
  dsimp only
  rw [ParticipantOpenHighLowLastIndicator.decode_encode, some_bind]
  rfl

end LongTradeMessage

/-- Trading Status Message: 72 bytes -/
structure TradingStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  lastPrice : BitVec 64
  highIndicationPriceUpperLimitPriceBand : BitVec 64
  lowIndicationPriceLowerLimitPriceBand : BitVec 64
  buyVolume : BitVec 32
  sellVolume : BitVec 32
  securityStatus : SecurityStatus
  haltReason : HaltReason
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  limitUpLimitDownIndicator : LimitUpLimitDownIndicator
  deriving DecidableEq, Repr

namespace TradingStatusMessage

def encode (message : TradingStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.highIndicationPriceUpperLimitPriceBand
    ++ (encodeUInt 8 message.lowIndicationPriceLowerLimitPriceBand
    ++ (encodeUInt 4 message.buyVolume
    ++ (encodeUInt 4 message.sellVolume
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltReason.encode message.haltReason
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (LimitUpLimitDownIndicator.encode message.limitUpLimitDownIndicator)))))))))))))))))

def decode (bytes : List UInt8) : Option (TradingStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (highIndicationPriceUpperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPriceLowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (buyVolume, bytes) ← decodeUInt 4 bytes
  let (sellVolume, bytes) ← decodeUInt 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (limitUpLimitDownIndicator, bytes) ← LimitUpLimitDownIndicator.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, lastPrice, highIndicationPriceUpperLimitPriceBand, lowIndicationPriceLowerLimitPriceBand, buyVolume, sellVolume, securityStatus, haltReason, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, limitUpLimitDownIndicator }, bytes)

@[simp] theorem encode_length (message : TradingStatusMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, SecurityStatus.encode_length, HaltReason.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, LimitUpLimitDownIndicator.encode_length]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [LimitUpLimitDownIndicator.decode_encode, some_bind]
  rfl

end TradingStatusMessage

/-- Short Trade Message: 36 bytes -/
structure ShortTradeMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbolShort : Alpha 5
  saleCondition : SaleCondition
  saleConditionCategory : SaleConditionCategory
  tradePriceShort : BitVec 16
  tradeVolumeShort : BitVec 16
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  consolidatedHighLowLastIndicator : ConsolidatedHighLowLastIndicator
  participantOpenHighLowLastIndicator : ParticipantOpenHighLowLastIndicator
  deriving DecidableEq, Repr

namespace ShortTradeMessage

def encode (message : ShortTradeMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolShort
    ++ (SaleCondition.encode message.saleCondition
    ++ (SaleConditionCategory.encode message.saleConditionCategory
    ++ (encodeUInt 2 message.tradePriceShort
    ++ (encodeUInt 2 message.tradeVolumeShort
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (ConsolidatedHighLowLastIndicator.encode message.consolidatedHighLowLastIndicator
    ++ (ParticipantOpenHighLowLastIndicator.encode message.participantOpenHighLowLastIndicator))))))))))))

def decode (bytes : List UInt8) : Option (ShortTradeMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbolShort, bytes) ← Alpha.decode 5 bytes
  let (saleCondition, bytes) ← SaleCondition.decode bytes
  let (saleConditionCategory, bytes) ← SaleConditionCategory.decode bytes
  let (tradePriceShort, bytes) ← decodeUInt 2 bytes
  let (tradeVolumeShort, bytes) ← decodeUInt 2 bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (consolidatedHighLowLastIndicator, bytes) ← ConsolidatedHighLowLastIndicator.decode bytes
  let (participantOpenHighLowLastIndicator, bytes) ← ParticipantOpenHighLowLastIndicator.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbolShort, saleCondition, saleConditionCategory, tradePriceShort, tradeVolumeShort, primaryListingMarketParticipantId, consolidatedHighLowLastIndicator, participantOpenHighLowLastIndicator }, bytes)

@[simp] theorem encode_length (message : ShortTradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, SaleCondition.encode_length, SaleConditionCategory.encode_length, PrimaryListingMarketParticipantId.encode_length, ConsolidatedHighLowLastIndicator.encode_length, ParticipantOpenHighLowLastIndicator.encode_length]

theorem encode_length_pos (message : ShortTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedHighLowLastIndicator.decode_encode, some_bind]
  dsimp only
  rw [ParticipantOpenHighLowLastIndicator.decode_encode, some_bind]
  rfl

end ShortTradeMessage

/-- Trade Cancel Error Message: 150 bytes -/
structure TradeCancelErrorMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleConditions : SaleConditions
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  originalParticipantReferenceNumber : BitVec 64
  timestamp2 : Timestamp2
  cancelErrorAction : CancelErrorAction
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  consolidatedData : ConsolidatedData
  participantData : ParticipantData
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (SaleConditions.encode message.saleConditions
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (encodeUInt 8 message.originalParticipantReferenceNumber
    ++ (Timestamp2.encode message.timestamp2
    ++ (CancelErrorAction.encode message.cancelErrorAction
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ConsolidatedData.encode message.consolidatedData
    ++ (ParticipantData.encode message.participantData)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleConditions, bytes) ← SaleConditions.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (originalParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (cancelErrorAction, bytes) ← CancelErrorAction.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (consolidatedData, bytes) ← ConsolidatedData.decode bytes
  let (participantData, bytes) ← ParticipantData.decode bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, saleConditions, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, tradeReportingFacilityId, originalParticipantReferenceNumber, timestamp2, cancelErrorAction, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, consolidatedData, participantData }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 150 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, SaleConditions.encode_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length, CancelErrorAction.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, ConsolidatedData.encode_length, ParticipantData.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelErrorAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedData.decode_encode, some_bind]
  dsimp only
  rw [ParticipantData.decode_encode, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Any Trade Message Payload, selected by Trade Message Type -/
inductive TradeMessagePayload where
  | auctionStatusMessage (message : AuctionStatusMessage) -- "A" 0x41
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  | longTradeMessage (message : LongTradeMessage) -- "L" 0x4C
  | tradingStatusMessage (message : TradingStatusMessage) -- "S" 0x53
  | shortTradeMessage (message : ShortTradeMessage) -- "T" 0x54
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace TradeMessagePayload

/-- The Trade Message Type each message is sent under -/
def tag : TradeMessagePayload → BitVec 8
  | .auctionStatusMessage _ => 65
  | .tradeCorrectionMessage _ => 67
  | .longTradeMessage _ => 76
  | .tradingStatusMessage _ => 83
  | .shortTradeMessage _ => 84
  | .tradeCancelErrorMessage _ => 88

def encode : TradeMessagePayload → List UInt8
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .longTradeMessage message => LongTradeMessage.encode message
  | .tradingStatusMessage message => TradingStatusMessage.encode message
  | .shortTradeMessage message => ShortTradeMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : TradeMessagePayload) : (encode message).length ≤ 185 := by
  cases message with
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | longTradeMessage inner =>
    simp only [encode, LongTradeMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [encode, TradingStatusMessage.encode_length]
    omega
  | shortTradeMessage inner =>
    simp only [encode, ShortTradeMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (TradeMessagePayload × List UInt8) :=
  if tag = 65 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 76 then (LongTradeMessage.decode bytes).map fun (message, rest) => (.longTradeMessage message, rest)
  else if tag = 83 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else if tag = 84 then (ShortTradeMessage.decode bytes).map fun (message, rest) => (.shortTradeMessage message, rest)
  else if tag = 88 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : TradeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end TradeMessagePayload

/-- Trade Message -/
structure TradeMessage where
  tradeMessagePayload : TradeMessagePayload
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 1 (TradeMessagePayload.tag message.tradeMessagePayload)
    ++ (TradeMessagePayload.encode message.tradeMessagePayload)

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (tradeMessageType, bytes) ← decodeUInt 1 bytes
  let (tradeMessagePayload, bytes) ← TradeMessagePayload.decode tradeMessageType bytes
  pure ({ tradeMessagePayload }, bytes)

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeMessage) : (encode message).length ≤ 186 := by
  unfold encode
  cases message.tradeMessagePayload with
  | auctionStatusMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | longTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, LongTradeMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradingStatusMessage.encode_length]
    omega
  | shortTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, ShortTradeMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeMessagePayload.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | indicesMessage (message : IndicesMessage) -- "I" 0x49
  | marketStatusMessage (message : MarketStatusMessage) -- "M" 0x4D
  | priorDayMessage (message : PriorDayMessage) -- "P" 0x50
  | summaryMessage (message : SummaryMessage) -- "S" 0x53
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67
  | .indicesMessage _ => 73
  | .marketStatusMessage _ => 77
  | .priorDayMessage _ => 80
  | .summaryMessage _ => 83
  | .tradeMessage _ => 84

def encode : CategoryPayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message
  | .indicesMessage message => IndicesMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .priorDayMessage message => PriorDayMessage.encode message
  | .summaryMessage message => SummaryMessage.encode message
  | .tradeMessage message => TradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 2319 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega
  | indicesMessage inner =>
    have bound_inner := IndicesMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [encode]
    omega
  | priorDayMessage inner =>
    have bound_inner := PriorDayMessage.encode_length_le inner
    simp only [encode]
    omega
  | summaryMessage inner =>
    have bound_inner := SummaryMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 73 then (IndicesMessage.decode bytes).map fun (message, rest) => (.indicesMessage message, rest)
  else if tag = 77 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 80 then (PriorDayMessage.decode bytes).map fun (message, rest) => (.priorDayMessage message, rest)
  else if tag = 83 then (SummaryMessage.decode bytes).map fun (message, rest) => (.summaryMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageLength
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (CategoryPayload.encode message.categoryPayload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ messageLength, categoryPayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 2322 := by
  unfold encode
  cases message.categoryPayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | indicesMessage inner =>
    have bound_inner := IndicesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | priorDayMessage inner =>
    have bound_inner := PriorDayMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | summaryMessage inner =>
    have bound_inner := SummaryMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  dataFeedIndicator : Alpha 1
  retransmissionIndicator : RetransmissionIndicator
  blockSequenceNumber : BitVec 32
  sipBlockTimestamp : SipBlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (Alpha.encode message.dataFeedIndicator
    ++ (RetransmissionIndicator.encode message.retransmissionIndicator
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (SipBlockTimestamp.encode message.sipBlockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (dataFeedIndicator, bytes) ← Alpha.decode 1 bytes
  let (retransmissionIndicator, bytes) ← RetransmissionIndicator.decode bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (sipBlockTimestamp, bytes) ← SipBlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, dataFeedIndicator, retransmissionIndicator, blockSequenceNumber, sipBlockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 592131 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 2322 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIndicator.encode_length, SipBlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RetransmissionIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SipBlockTimestamp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacCtsOutputCtaV191
