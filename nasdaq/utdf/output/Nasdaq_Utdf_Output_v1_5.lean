import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Output v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqUtdfOutputUtpV15

/-- Market Center Originator Id: one byte code -/
def MarketCenterOriginatorId.codes : List UInt8 :=
  [0x59, 0x5A, 0x4A, 0x4B, 0x57, 0x42, 0x58, 0x51, 0x49, 0x4E, 0x50, 0x41, 0x43, 0x4D, 0x44, 0x56, 0x4C, 0x48, 0x55, 0x45]

inductive MarketCenterOriginatorId where
  | byx -- Byx
  | bzx -- Bzx
  | edga -- Edga
  | edgx -- Edgx
  | cboe -- Cboe
  | bx -- Bx
  | phlx -- Phlx
  | nasdaq -- Nasdaq
  | ise -- Ise
  | nyse -- Nyse
  | arca -- Arca
  | american -- American
  | national -- National
  | chicago -- Chicago
  | finra -- Finra
  | iex -- Iex
  | ltse -- Ltse
  | pearl -- Pearl
  | memx -- Memx
  | marketIndependent -- Market Independent
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenterOriginatorId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenterOriginatorId

def toByte : MarketCenterOriginatorId → UInt8
  | .byx => 0x59
  | .bzx => 0x5A
  | .edga => 0x4A
  | .edgx => 0x4B
  | .cboe => 0x57
  | .bx => 0x42
  | .phlx => 0x58
  | .nasdaq => 0x51
  | .ise => 0x49
  | .nyse => 0x4E
  | .arca => 0x50
  | .american => 0x41
  | .national => 0x43
  | .chicago => 0x4D
  | .finra => 0x44
  | .iex => 0x56
  | .ltse => 0x4C
  | .pearl => 0x48
  | .memx => 0x55
  | .marketIndependent => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenterOriginatorId :=
  if byte = 0x59 then .byx
  else if byte = 0x5A then .bzx
  else if byte = 0x4A then .edga
  else if byte = 0x4B then .edgx
  else if byte = 0x57 then .cboe
  else if byte = 0x42 then .bx
  else if byte = 0x58 then .phlx
  else if byte = 0x51 then .nasdaq
  else if byte = 0x49 then .ise
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .arca
  else if byte = 0x41 then .american
  else if byte = 0x43 then .national
  else if byte = 0x4D then .chicago
  else if byte = 0x44 then .finra
  else if byte = 0x56 then .iex
  else if byte = 0x4C then .ltse
  else if byte = 0x48 then .pearl
  else if byte = 0x55 then .memx
  else .marketIndependent

def ofByte (byte : UInt8) : MarketCenterOriginatorId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenterOriginatorId) : ofByte value.toByte = value := by
  cases value with
  | byx => decide
  | bzx => decide
  | edga => decide
  | edgx => decide
  | cboe => decide
  | bx => decide
  | phlx => decide
  | nasdaq => decide
  | ise => decide
  | nyse => decide
  | arca => decide
  | american => decide
  | national => decide
  | chicago => decide
  | finra => decide
  | iex => decide
  | ltse => decide
  | pearl => decide
  | memx => decide
  | marketIndependent => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenterOriginatorId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenterOriginatorId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenterOriginatorId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenterOriginatorId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenterOriginatorId

/-- Sub Market Center Id: one byte code -/
def SubMarketCenterId.codes : List UInt8 :=
  [0x4E, 0x51, 0x42, 0x20]

inductive SubMarketCenterId where
  | nyseTrf -- Nyse Trf
  | nasdaqTrfCarteret -- Nasdaq Trf Carteret
  | nasdaqTrfChicago -- Nasdaq Trf Chicago
  | finraAlternativeDisplayFacility -- Finra Alternative Display Facility
  | unlisted (byte : { byte : UInt8 // byte ∉ SubMarketCenterId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SubMarketCenterId

def toByte : SubMarketCenterId → UInt8
  | .nyseTrf => 0x4E
  | .nasdaqTrfCarteret => 0x51
  | .nasdaqTrfChicago => 0x42
  | .finraAlternativeDisplayFacility => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SubMarketCenterId :=
  if byte = 0x4E then .nyseTrf
  else if byte = 0x51 then .nasdaqTrfCarteret
  else if byte = 0x42 then .nasdaqTrfChicago
  else .finraAlternativeDisplayFacility

def ofByte (byte : UInt8) : SubMarketCenterId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SubMarketCenterId) : ofByte value.toByte = value := by
  cases value with
  | nyseTrf => decide
  | nasdaqTrfCarteret => decide
  | nasdaqTrfChicago => decide
  | finraAlternativeDisplayFacility => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SubMarketCenterId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SubMarketCenterId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SubMarketCenterId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SubMarketCenterId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SubMarketCenterId

/-- Level 1: one byte code -/
def Level1.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52, 0x59, 0x20]

inductive Level1 where
  | regularTrade -- Regular Trade
  | cash -- Cash
  | nextDay -- Next Day
  | seller -- Seller
  | yellowFlag -- Yellow Flag
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ Level1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Level1

def toByte : Level1 → UInt8
  | .regularTrade => 0x40
  | .cash => 0x43
  | .nextDay => 0x4E
  | .seller => 0x52
  | .yellowFlag => 0x59
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Level1 :=
  if byte = 0x40 then .regularTrade
  else if byte = 0x43 then .cash
  else if byte = 0x4E then .nextDay
  else if byte = 0x52 then .seller
  else if byte = 0x59 then .yellowFlag
  else .notAvailable

def ofByte (byte : UInt8) : Level1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Level1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | cash => decide
  | nextDay => decide
  | seller => decide
  | yellowFlag => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Level1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Level1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Level1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Level1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Level1

/-- Level 2: one byte code -/
def Level2.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x20]

inductive Level2 where
  | intermarketSweep -- Intermarket Sweep
  | openingPrints -- Opening Prints
  | derivativelyPriced -- Derivatively Priced
  | reOpeningPrints -- Re Opening Prints
  | closingPrints -- Closing Prints
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | placeholderFor611Exempt -- Placeholder For 611 Exempt
  | correctedConsolidatedClose -- Corrected Consolidated Close
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ Level2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Level2

def toByte : Level2 → UInt8
  | .intermarketSweep => 0x46
  | .openingPrints => 0x4F
  | .derivativelyPriced => 0x34
  | .reOpeningPrints => 0x35
  | .closingPrints => 0x36
  | .qualifiedContingentTrade => 0x37
  | .placeholderFor611Exempt => 0x38
  | .correctedConsolidatedClose => 0x39
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Level2 :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrints
  else if byte = 0x34 then .derivativelyPriced
  else if byte = 0x35 then .reOpeningPrints
  else if byte = 0x36 then .closingPrints
  else if byte = 0x37 then .qualifiedContingentTrade
  else if byte = 0x38 then .placeholderFor611Exempt
  else if byte = 0x39 then .correctedConsolidatedClose
  else .notAvailable

def ofByte (byte : UInt8) : Level2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Level2) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrints => decide
  | derivativelyPriced => decide
  | reOpeningPrints => decide
  | closingPrints => decide
  | qualifiedContingentTrade => decide
  | placeholderFor611Exempt => decide
  | correctedConsolidatedClose => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Level2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Level2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Level2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Level2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Level2

/-- Level 3: one byte code -/
def Level3.codes : List UInt8 :=
  [0x54, 0x4C, 0x5A, 0x55, 0x20, 0x31, 0x41, 0x42, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4B, 0x4D, 0x50, 0x51, 0x53, 0x56, 0x57, 0x58]

inductive Level3 where
  | formT -- Form T
  | soldLast -- Sold Last
  | soldOutOfSequence -- Sold Out Of Sequence
  | extendedTradingHours -- Extended Trading Hours
  | notAvailable -- Not Available
  | stoppedStock -- Stopped Stock
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | placeholderFuture -- Placeholder Future
  | bunchedSoldTrade -- Bunched Sold Trade
  | priceVariation -- Price Variation
  | oddLotTrade -- Odd Lot Trade
  | rule155 -- Rule 155
  | marketCenterOfficialClosePrice -- Market Center Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | marketCenterOfficialOpenPrice -- Market Center Official Open Price
  | splitTrade -- Split Trade
  | contingentTrade -- Contingent Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ Level3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Level3

def toByte : Level3 → UInt8
  | .formT => 0x54
  | .soldLast => 0x4C
  | .soldOutOfSequence => 0x5A
  | .extendedTradingHours => 0x55
  | .notAvailable => 0x20
  | .stoppedStock => 0x31
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .placeholderFuture => 0x45
  | .bunchedSoldTrade => 0x47
  | .priceVariation => 0x48
  | .oddLotTrade => 0x49
  | .rule155 => 0x4B
  | .marketCenterOfficialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .marketCenterOfficialOpenPrice => 0x51
  | .splitTrade => 0x53
  | .contingentTrade => 0x56
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Level3 :=
  if byte = 0x54 then .formT
  else if byte = 0x4C then .soldLast
  else if byte = 0x5A then .soldOutOfSequence
  else if byte = 0x55 then .extendedTradingHours
  else if byte = 0x20 then .notAvailable
  else if byte = 0x31 then .stoppedStock
  else if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x45 then .placeholderFuture
  else if byte = 0x47 then .bunchedSoldTrade
  else if byte = 0x48 then .priceVariation
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4B then .rule155
  else if byte = 0x4D then .marketCenterOfficialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .marketCenterOfficialOpenPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x56 then .contingentTrade
  else if byte = 0x57 then .averagePriceTrade
  else .crossTrade

def ofByte (byte : UInt8) : Level3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Level3) : ofByte value.toByte = value := by
  cases value with
  | formT => decide
  | soldLast => decide
  | soldOutOfSequence => decide
  | extendedTradingHours => decide
  | notAvailable => decide
  | stoppedStock => decide
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | placeholderFuture => decide
  | bunchedSoldTrade => decide
  | priceVariation => decide
  | oddLotTrade => decide
  | rule155 => decide
  | marketCenterOfficialClosePrice => decide
  | priorReferencePrice => decide
  | marketCenterOfficialOpenPrice => decide
  | splitTrade => decide
  | contingentTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Level3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Level3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Level3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Level3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Level3

/-- Consolidated Price Change Indicator: one byte code -/
def ConsolidatedPriceChangeIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37]

inductive ConsolidatedPriceChangeIndicator where
  | noPricesChanged -- No Prices Changed
  | consolidatedLastPriceChanged -- Consolidated Last Price Changed
  | consolidatedLowPriceChanged -- Consolidated Low Price Changed
  | consolidatedLastAndConsolidatedLowPricesChanged -- Consolidated Last And Consolidated Low Prices Changed
  | consolidatedHighPriceChanged -- Consolidated High Price Changed
  | consolidatedLastAndConsolidatedHighPricesChanged -- Consolidated Last And Consolidated High Prices Changed
  | consolidatedHighAndConsolidatedLowPricesChanged -- Consolidated High And Consolidated Low Prices Changed
  | allConsolidatedPricesChanged -- All Consolidated Prices Changed
  | unlisted (byte : { byte : UInt8 // byte ∉ ConsolidatedPriceChangeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConsolidatedPriceChangeIndicator

def toByte : ConsolidatedPriceChangeIndicator → UInt8
  | .noPricesChanged => 0x30
  | .consolidatedLastPriceChanged => 0x31
  | .consolidatedLowPriceChanged => 0x32
  | .consolidatedLastAndConsolidatedLowPricesChanged => 0x33
  | .consolidatedHighPriceChanged => 0x34
  | .consolidatedLastAndConsolidatedHighPricesChanged => 0x35
  | .consolidatedHighAndConsolidatedLowPricesChanged => 0x36
  | .allConsolidatedPricesChanged => 0x37
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ConsolidatedPriceChangeIndicator :=
  if byte = 0x30 then .noPricesChanged
  else if byte = 0x31 then .consolidatedLastPriceChanged
  else if byte = 0x32 then .consolidatedLowPriceChanged
  else if byte = 0x33 then .consolidatedLastAndConsolidatedLowPricesChanged
  else if byte = 0x34 then .consolidatedHighPriceChanged
  else if byte = 0x35 then .consolidatedLastAndConsolidatedHighPricesChanged
  else if byte = 0x36 then .consolidatedHighAndConsolidatedLowPricesChanged
  else .allConsolidatedPricesChanged

def ofByte (byte : UInt8) : ConsolidatedPriceChangeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConsolidatedPriceChangeIndicator) : ofByte value.toByte = value := by
  cases value with
  | noPricesChanged => decide
  | consolidatedLastPriceChanged => decide
  | consolidatedLowPriceChanged => decide
  | consolidatedLastAndConsolidatedLowPricesChanged => decide
  | consolidatedHighPriceChanged => decide
  | consolidatedLastAndConsolidatedHighPricesChanged => decide
  | consolidatedHighAndConsolidatedLowPricesChanged => decide
  | allConsolidatedPricesChanged => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ConsolidatedPriceChangeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConsolidatedPriceChangeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConsolidatedPriceChangeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ConsolidatedPriceChangeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConsolidatedPriceChangeIndicator

/-- Participant Price Change Indicator: one byte code -/
def ParticipantPriceChangeIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37]

inductive ParticipantPriceChangeIndicator where
  | noPricesChanged -- No Prices Changed
  | participantLastPriceChanged -- Participant Last Price Changed
  | participantLowPriceChanged -- Participant Low Price Changed
  | participantLastAndLowPricesChanged -- Participant Last And Low Prices Changed
  | participantHighPriceChanged -- Participant High Price Changed
  | participantLastAndHighPricesChanged -- Participant Last And High Prices Changed
  | participantHighAndLowPricesChanged -- Participant High And Low Prices Changed
  | allParticipantPricesChanged -- All Participant Prices Changed
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantPriceChangeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantPriceChangeIndicator

def toByte : ParticipantPriceChangeIndicator → UInt8
  | .noPricesChanged => 0x30
  | .participantLastPriceChanged => 0x31
  | .participantLowPriceChanged => 0x32
  | .participantLastAndLowPricesChanged => 0x33
  | .participantHighPriceChanged => 0x34
  | .participantLastAndHighPricesChanged => 0x35
  | .participantHighAndLowPricesChanged => 0x36
  | .allParticipantPricesChanged => 0x37
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantPriceChangeIndicator :=
  if byte = 0x30 then .noPricesChanged
  else if byte = 0x31 then .participantLastPriceChanged
  else if byte = 0x32 then .participantLowPriceChanged
  else if byte = 0x33 then .participantLastAndLowPricesChanged
  else if byte = 0x34 then .participantHighPriceChanged
  else if byte = 0x35 then .participantLastAndHighPricesChanged
  else if byte = 0x36 then .participantHighAndLowPricesChanged
  else .allParticipantPricesChanged

def ofByte (byte : UInt8) : ParticipantPriceChangeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantPriceChangeIndicator) : ofByte value.toByte = value := by
  cases value with
  | noPricesChanged => decide
  | participantLastPriceChanged => decide
  | participantLowPriceChanged => decide
  | participantLastAndLowPricesChanged => decide
  | participantHighPriceChanged => decide
  | participantLastAndHighPricesChanged => decide
  | participantHighAndLowPricesChanged => decide
  | allParticipantPricesChanged => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantPriceChangeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantPriceChangeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantPriceChangeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantPriceChangeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantPriceChangeIndicator

/-- As Of Action: one byte code -/
def AsOfAction.codes : List UInt8 :=
  [0x41, 0x43]

inductive AsOfAction where
  | tradeAddition -- Trade Addition
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ AsOfAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AsOfAction

def toByte : AsOfAction → UInt8
  | .tradeAddition => 0x41
  | .tradeCancel => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AsOfAction :=
  if byte = 0x41 then .tradeAddition
  else .tradeCancel

def ofByte (byte : UInt8) : AsOfAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AsOfAction) : ofByte value.toByte = value := by
  cases value with
  | tradeAddition => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AsOfAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AsOfAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AsOfAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AsOfAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AsOfAction

/-- Trading Action Code: one byte code -/
def TradingActionCode.codes : List UInt8 :=
  [0x48, 0x51, 0x54, 0x50]

inductive TradingActionCode where
  | tradingHalt -- Trading Halt
  | quotationResumptionIncludingAfterEma -- Quotation Resumption Including After Ema
  | tradingResumption -- Trading Resumption
  | volatilityTradingPause -- Volatility Trading Pause
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingActionCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingActionCode

def toByte : TradingActionCode → UInt8
  | .tradingHalt => 0x48
  | .quotationResumptionIncludingAfterEma => 0x51
  | .tradingResumption => 0x54
  | .volatilityTradingPause => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingActionCode :=
  if byte = 0x48 then .tradingHalt
  else if byte = 0x51 then .quotationResumptionIncludingAfterEma
  else if byte = 0x54 then .tradingResumption
  else .volatilityTradingPause

def ofByte (byte : UInt8) : TradingActionCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingActionCode) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | quotationResumptionIncludingAfterEma => decide
  | tradingResumption => decide
  | volatilityTradingPause => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingActionCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingActionCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingActionCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingActionCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingActionCode

/-- Issue Type: one byte code -/
def IssueType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x49, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive IssueType where
  | americanDepositoryReceipt -- American Depository Receipt
  | bond -- Bond
  | commonStock -- Common Stock
  | depositoryReceipt -- Depository Receipt
  | rule144a -- Rule 144a
  | limitedPartnership -- Limited Partnership
  | note -- Note
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | otherSecurities -- Other Securities
  | rights -- Rights
  | sharesOfBeneficialInterest -- Shares Of Beneficial Interest
  | convertibleDebenture -- Convertible Debenture
  | unit -- Unit
  | unitsOfBeneficialInterest -- Units Of Beneficial Interest
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ IssueType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IssueType

def toByte : IssueType → UInt8
  | .americanDepositoryReceipt => 0x41
  | .bond => 0x42
  | .commonStock => 0x43
  | .depositoryReceipt => 0x46
  | .rule144a => 0x49
  | .limitedPartnership => 0x4C
  | .note => 0x4E
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .otherSecurities => 0x51
  | .rights => 0x52
  | .sharesOfBeneficialInterest => 0x53
  | .convertibleDebenture => 0x54
  | .unit => 0x55
  | .unitsOfBeneficialInterest => 0x56
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IssueType :=
  if byte = 0x41 then .americanDepositoryReceipt
  else if byte = 0x42 then .bond
  else if byte = 0x43 then .commonStock
  else if byte = 0x46 then .depositoryReceipt
  else if byte = 0x49 then .rule144a
  else if byte = 0x4C then .limitedPartnership
  else if byte = 0x4E then .note
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x51 then .otherSecurities
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficialInterest
  else if byte = 0x54 then .convertibleDebenture
  else if byte = 0x55 then .unit
  else if byte = 0x56 then .unitsOfBeneficialInterest
  else .warrant

def ofByte (byte : UInt8) : IssueType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IssueType) : ofByte value.toByte = value := by
  cases value with
  | americanDepositoryReceipt => decide
  | bond => decide
  | commonStock => decide
  | depositoryReceipt => decide
  | rule144a => decide
  | limitedPartnership => decide
  | note => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | otherSecurities => decide
  | rights => decide
  | sharesOfBeneficialInterest => decide
  | convertibleDebenture => decide
  | unit => decide
  | unitsOfBeneficialInterest => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IssueType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IssueType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IssueType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IssueType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IssueType

/-- Market Tier: one byte code -/
def MarketTier.codes : List UInt8 :=
  [0x51, 0x47, 0x53]

inductive MarketTier where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketTier

def toByte : MarketTier → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketTier :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else .nasdaqCapitalMarket

def ofByte (byte : UInt8) : MarketTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketTier) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketTier

/-- Authenticity: one byte code -/
def Authenticity.codes : List UInt8 :=
  [0x50, 0x54, 0x44, 0x58]

inductive Authenticity where
  | production -- Production
  | test -- Test
  | demo -- Demo
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .production => 0x50
  | .test => 0x54
  | .demo => 0x44
  | .deleted => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .production
  else if byte = 0x54 then .test
  else if byte = 0x44 then .demo
  else .deleted

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | production => decide
  | test => decide
  | demo => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Authenticity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Authenticity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Authenticity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Authenticity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Authenticity

/-- Short Sale Threshold Indicator: one byte code -/
def ShortSaleThresholdIndicator.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive ShortSaleThresholdIndicator where
  | issueIsRestricted -- Issue Is Restricted
  | issueIsNotRestricted -- Issue Is Not Restricted
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleThresholdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .issueIsRestricted => 0x59
  | .issueIsNotRestricted => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleThresholdIndicator :=
  if byte = 0x59 then .issueIsRestricted
  else if byte = 0x4E then .issueIsNotRestricted
  else .notAvailable

def ofByte (byte : UInt8) : ShortSaleThresholdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleThresholdIndicator) : ofByte value.toByte = value := by
  cases value with
  | issueIsRestricted => decide
  | issueIsNotRestricted => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleThresholdIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleThresholdIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleThresholdIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleThresholdIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleThresholdIndicator

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x43, 0x44, 0x45, 0x51, 0x4E, 0x47, 0x48, 0x4A, 0x4B]

inductive FinancialStatusIndicator where
  | creationsAndOrRedemptionsSuspended -- Creations And Or Redemptions Suspended
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | normal -- Normal
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .creationsAndOrRedemptionsSuspended => 0x43
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .normal => 0x4E
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x43 then .creationsAndOrRedemptionsSuspended
  else if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x4E then .normal
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else .deficientDelinquentAndBankrupt

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | creationsAndOrRedemptionsSuspended => decide
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | normal => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
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

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTestInEffect -- No Price Test In Effect
  | regShoInEffectDueToAnIntraDayPriceDrop -- Reg Sho In Effect Due To An Intra Day Price Drop
  | regShoRestrictionRemainsInEffect -- Reg Sho Restriction Remains In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTestInEffect => 0x30
  | .regShoInEffectDueToAnIntraDayPriceDrop => 0x31
  | .regShoRestrictionRemainsInEffect => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTestInEffect
  else if byte = 0x31 then .regShoInEffectDueToAnIntraDayPriceDrop
  else .regShoRestrictionRemainsInEffect

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTestInEffect => decide
  | regShoInEffectDueToAnIntraDayPriceDrop => decide
  | regShoRestrictionRemainsInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RegShoAction

/-- Luld Price Band Indicator: one byte code -/
def LuldPriceBandIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x20]

inductive LuldPriceBandIndicator where
  | openingUpdate -- Opening Update
  | intraDayUpdate -- Intra Day Update
  | restatedValue -- Restated Value
  | suspendedDuringTradingHaltOrTradingPause -- Suspended During Trading Halt Or Trading Pause
  | reOpeningUpdate -- Re Opening Update
  | outsidePriceBandRuleHours -- Outside Price Band Rule Hours
  | noneProvided -- None Provided
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldPriceBandIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldPriceBandIndicator

def toByte : LuldPriceBandIndicator → UInt8
  | .openingUpdate => 0x41
  | .intraDayUpdate => 0x42
  | .restatedValue => 0x43
  | .suspendedDuringTradingHaltOrTradingPause => 0x44
  | .reOpeningUpdate => 0x45
  | .outsidePriceBandRuleHours => 0x46
  | .noneProvided => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldPriceBandIndicator :=
  if byte = 0x41 then .openingUpdate
  else if byte = 0x42 then .intraDayUpdate
  else if byte = 0x43 then .restatedValue
  else if byte = 0x44 then .suspendedDuringTradingHaltOrTradingPause
  else if byte = 0x45 then .reOpeningUpdate
  else if byte = 0x46 then .outsidePriceBandRuleHours
  else .noneProvided

def ofByte (byte : UInt8) : LuldPriceBandIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldPriceBandIndicator) : ofByte value.toByte = value := by
  cases value with
  | openingUpdate => decide
  | intraDayUpdate => decide
  | restatedValue => decide
  | suspendedDuringTradingHaltOrTradingPause => decide
  | reOpeningUpdate => decide
  | outsidePriceBandRuleHours => decide
  | noneProvided => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldPriceBandIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldPriceBandIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldPriceBandIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldPriceBandIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldPriceBandIndicator

/-- Mwcb Status Level Indicator: one byte code -/
def MwcbStatusLevelIndicator.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive MwcbStatusLevelIndicator where
  | level1Breached -- Level 1 Breached
  | level2Breached -- Level 2 Breached
  | level3Breached -- Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ MwcbStatusLevelIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MwcbStatusLevelIndicator

def toByte : MwcbStatusLevelIndicator → UInt8
  | .level1Breached => 0x31
  | .level2Breached => 0x32
  | .level3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MwcbStatusLevelIndicator :=
  if byte = 0x31 then .level1Breached
  else if byte = 0x32 then .level2Breached
  else .level3Breached

def ofByte (byte : UInt8) : MwcbStatusLevelIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MwcbStatusLevelIndicator) : ofByte value.toByte = value := by
  cases value with
  | level1Breached => decide
  | level2Breached => decide
  | level3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MwcbStatusLevelIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MwcbStatusLevelIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MwcbStatusLevelIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MwcbStatusLevelIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MwcbStatusLevelIndicator

/-- Trading Action Indicator: one byte code -/
def TradingActionIndicator.codes : List UInt8 :=
  [0x48, 0x20]

inductive TradingActionIndicator where
  | tradingHalt -- Trading Halt
  | regularTrading -- Regular Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingActionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingActionIndicator

def toByte : TradingActionIndicator → UInt8
  | .tradingHalt => 0x48
  | .regularTrading => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingActionIndicator :=
  if byte = 0x48 then .tradingHalt
  else .regularTrading

def ofByte (byte : UInt8) : TradingActionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingActionIndicator) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | regularTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingActionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingActionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingActionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingActionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingActionIndicator

/-- Market Center Close Indicator: one byte code -/
def MarketCenterCloseIndicator.codes : List UInt8 :=
  [0x4D, 0x20]

inductive MarketCenterCloseIndicator where
  | basedOnMSaleCondition -- Based On M Sale Condition
  | notBasedOnMSaleCondition -- Not Based On M Sale Condition
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenterCloseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenterCloseIndicator

def toByte : MarketCenterCloseIndicator → UInt8
  | .basedOnMSaleCondition => 0x4D
  | .notBasedOnMSaleCondition => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenterCloseIndicator :=
  if byte = 0x4D then .basedOnMSaleCondition
  else .notBasedOnMSaleCondition

def ofByte (byte : UInt8) : MarketCenterCloseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenterCloseIndicator) : ofByte value.toByte = value := by
  cases value with
  | basedOnMSaleCondition => decide
  | notBasedOnMSaleCondition => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenterCloseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenterCloseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenterCloseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenterCloseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenterCloseIndicator

/-- Message Info: 26 bytes -/
structure MessageInfo where
  marketCenterOriginatorId : MarketCenterOriginatorId
  subMarketCenterId : SubMarketCenterId
  sipTimestamp : BitVec 64
  participantTimestamp : BitVec 64
  participantToken : BitVec 64
  deriving DecidableEq, Repr

namespace MessageInfo

def encode (message : MessageInfo) : List UInt8 :=
  MarketCenterOriginatorId.encode message.marketCenterOriginatorId
    ++ (SubMarketCenterId.encode message.subMarketCenterId
    ++ (encodeUInt 8 message.sipTimestamp
    ++ (encodeUInt 8 message.participantTimestamp
    ++ (encodeUInt 8 message.participantToken))))

def decode (bytes : List UInt8) : Option (MessageInfo × List UInt8) := do
  let (marketCenterOriginatorId, bytes) ← MarketCenterOriginatorId.decode bytes
  let (subMarketCenterId, bytes) ← SubMarketCenterId.decode bytes
  let (sipTimestamp, bytes) ← decodeUInt 8 bytes
  let (participantTimestamp, bytes) ← decodeUInt 8 bytes
  let (participantToken, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenterOriginatorId, subMarketCenterId, sipTimestamp, participantTimestamp, participantToken }, bytes)

@[simp] theorem encode_length (message : MessageInfo) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, MarketCenterOriginatorId.encode_length, SubMarketCenterId.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MessageInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterOriginatorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SubMarketCenterId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageInfo

/-- Sale Condition: 4 bytes -/
structure SaleCondition where
  level1 : Level1
  level2 : Level2
  level3 : Level3
  level4 : Alpha 1
  deriving DecidableEq, Repr

namespace SaleCondition

def encode (message : SaleCondition) : List UInt8 :=
  Level1.encode message.level1
    ++ (Level2.encode message.level2
    ++ (Level3.encode message.level3
    ++ (Alpha.encode message.level4)))

def decode (bytes : List UInt8) : Option (SaleCondition × List UInt8) := do
  let (level1, bytes) ← Level1.decode bytes
  let (level2, bytes) ← Level2.decode bytes
  let (level3, bytes) ← Level3.decode bytes
  let (level4, bytes) ← Alpha.decode 1 bytes
  pure ({ level1, level2, level3, level4 }, bytes)

@[simp] theorem encode_length (message : SaleCondition) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Level1.encode_length, Level2.encode_length, Level3.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SaleCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SaleCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Level1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level3.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SaleCondition

/-- Trade Report Message Short Form Message: 58 bytes -/
structure TradeReportMessageShortFormMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolShort : Alpha 5
  tradeId : BitVec 64
  tradePriceShort : BitVec 16
  tradeVolumeShort : BitVec 16
  saleCondition : SaleCondition
  tradeThroughExemptFlag : Alpha 1
  consolidatedPriceChangeIndicator : ConsolidatedPriceChangeIndicator
  participantPriceChangeIndicator : ParticipantPriceChangeIndicator
  deriving DecidableEq, Repr

namespace TradeReportMessageShortFormMessage

def encode (message : TradeReportMessageShortFormMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolShort
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 2 message.tradePriceShort
    ++ (encodeUInt 2 message.tradeVolumeShort
    ++ (SaleCondition.encode message.saleCondition
    ++ (Alpha.encode message.tradeThroughExemptFlag
    ++ (ConsolidatedPriceChangeIndicator.encode message.consolidatedPriceChangeIndicator
    ++ (ParticipantPriceChangeIndicator.encode message.participantPriceChangeIndicator)))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessageShortFormMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradePriceShort, bytes) ← decodeUInt 2 bytes
  let (tradeVolumeShort, bytes) ← decodeUInt 2 bytes
  let (saleCondition, bytes) ← SaleCondition.decode bytes
  let (tradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (consolidatedPriceChangeIndicator, bytes) ← ConsolidatedPriceChangeIndicator.decode bytes
  let (participantPriceChangeIndicator, bytes) ← ParticipantPriceChangeIndicator.decode bytes
  pure ({ messageInfo, finraTimestamp, symbolShort, tradeId, tradePriceShort, tradeVolumeShort, saleCondition, tradeThroughExemptFlag, consolidatedPriceChangeIndicator, participantPriceChangeIndicator }, bytes)

@[simp] theorem encode_length (message : TradeReportMessageShortFormMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, SaleCondition.encode_length, ConsolidatedPriceChangeIndicator.encode_length, ParticipantPriceChangeIndicator.encode_length]

theorem encode_length_pos (message : TradeReportMessageShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessageShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, SaleCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedPriceChangeIndicator.decode_encode, some_bind]
  dsimp only
  rw [ParticipantPriceChangeIndicator.decode_encode, some_bind]
  rfl

end TradeReportMessageShortFormMessage

/-- Trade Report Message Long Form Message: 74 bytes -/
structure TradeReportMessageLongFormMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 64
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  saleCondition : SaleCondition
  tradeThroughExemptFlag : Alpha 1
  sellersSaleDays : BitVec 16
  consolidatedPriceChangeIndicator : ConsolidatedPriceChangeIndicator
  participantPriceChangeIndicator : ParticipantPriceChangeIndicator
  deriving DecidableEq, Repr

namespace TradeReportMessageLongFormMessage

def encode (message : TradeReportMessageLongFormMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (SaleCondition.encode message.saleCondition
    ++ (Alpha.encode message.tradeThroughExemptFlag
    ++ (encodeUInt 2 message.sellersSaleDays
    ++ (ConsolidatedPriceChangeIndicator.encode message.consolidatedPriceChangeIndicator
    ++ (ParticipantPriceChangeIndicator.encode message.participantPriceChangeIndicator))))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessageLongFormMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (saleCondition, bytes) ← SaleCondition.decode bytes
  let (tradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 2 bytes
  let (consolidatedPriceChangeIndicator, bytes) ← ConsolidatedPriceChangeIndicator.decode bytes
  let (participantPriceChangeIndicator, bytes) ← ParticipantPriceChangeIndicator.decode bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, tradeId, tradePrice, tradeVolume, saleCondition, tradeThroughExemptFlag, sellersSaleDays, consolidatedPriceChangeIndicator, participantPriceChangeIndicator }, bytes)

@[simp] theorem encode_length (message : TradeReportMessageLongFormMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, SaleCondition.encode_length, ConsolidatedPriceChangeIndicator.encode_length, ParticipantPriceChangeIndicator.encode_length]

theorem encode_length_pos (message : TradeReportMessageLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessageLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, SaleCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ConsolidatedPriceChangeIndicator.decode_encode, some_bind]
  dsimp only
  rw [ParticipantPriceChangeIndicator.decode_encode, some_bind]
  rfl

end TradeReportMessageLongFormMessage

/-- Original Sale Condition: 4 bytes -/
structure OriginalSaleCondition where
  level1 : Level1
  level2 : Level2
  level3 : Level3
  level4 : Alpha 1
  deriving DecidableEq, Repr

namespace OriginalSaleCondition

def encode (message : OriginalSaleCondition) : List UInt8 :=
  Level1.encode message.level1
    ++ (Level2.encode message.level2
    ++ (Level3.encode message.level3
    ++ (Alpha.encode message.level4)))

def decode (bytes : List UInt8) : Option (OriginalSaleCondition × List UInt8) := do
  let (level1, bytes) ← Level1.decode bytes
  let (level2, bytes) ← Level2.decode bytes
  let (level3, bytes) ← Level3.decode bytes
  let (level4, bytes) ← Alpha.decode 1 bytes
  pure ({ level1, level2, level3, level4 }, bytes)

@[simp] theorem encode_length (message : OriginalSaleCondition) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Level1.encode_length, Level2.encode_length, Level3.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OriginalSaleCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalSaleCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Level1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level3.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OriginalSaleCondition

/-- Trade Cancel Error Message: 139 bytes -/
structure TradeCancelErrorMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  tradeCancellationType : Alpha 1
  originalTradeId : BitVec 64
  originalTradePrice : BitVec 64
  originalVolume : BitVec 32
  originalSaleCondition : OriginalSaleCondition
  originalTradeThroughExemptFlag : Alpha 1
  originalSellersSaleDays : BitVec 16
  consolidatedHighPrice : BitVec 64
  consolidatedLowPrice : BitVec 64
  consolidatedLastPrice : BitVec 64
  consolidatedVolume : BitVec 64
  consolidatedPriceChangeIndicator : ConsolidatedPriceChangeIndicator
  marketCenterOriginatorId : MarketCenterOriginatorId
  marketParticipantHighPrice : BitVec 64
  marketParticipantLowPrice : BitVec 64
  marketParticipantLastPrice : BitVec 64
  marketParticipantVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (Alpha.encode message.tradeCancellationType
    ++ (encodeUInt 8 message.originalTradeId
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalVolume
    ++ (OriginalSaleCondition.encode message.originalSaleCondition
    ++ (Alpha.encode message.originalTradeThroughExemptFlag
    ++ (encodeUInt 2 message.originalSellersSaleDays
    ++ (encodeUInt 8 message.consolidatedHighPrice
    ++ (encodeUInt 8 message.consolidatedLowPrice
    ++ (encodeUInt 8 message.consolidatedLastPrice
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (ConsolidatedPriceChangeIndicator.encode message.consolidatedPriceChangeIndicator
    ++ (MarketCenterOriginatorId.encode message.marketCenterOriginatorId
    ++ (encodeUInt 8 message.marketParticipantHighPrice
    ++ (encodeUInt 8 message.marketParticipantLowPrice
    ++ (encodeUInt 8 message.marketParticipantLastPrice
    ++ (encodeUInt 8 message.marketParticipantVolume)))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeCancellationType, bytes) ← Alpha.decode 1 bytes
  let (originalTradeId, bytes) ← decodeUInt 8 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (originalSaleCondition, bytes) ← OriginalSaleCondition.decode bytes
  let (originalTradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (originalSellersSaleDays, bytes) ← decodeUInt 2 bytes
  let (consolidatedHighPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedLowPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedLastPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (consolidatedPriceChangeIndicator, bytes) ← ConsolidatedPriceChangeIndicator.decode bytes
  let (marketCenterOriginatorId, bytes) ← MarketCenterOriginatorId.decode bytes
  let (marketParticipantHighPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantLowPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantLastPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantVolume, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, tradeCancellationType, originalTradeId, originalTradePrice, originalVolume, originalSaleCondition, originalTradeThroughExemptFlag, originalSellersSaleDays, consolidatedHighPrice, consolidatedLowPrice, consolidatedLastPrice, consolidatedVolume, consolidatedPriceChangeIndicator, marketCenterOriginatorId, marketParticipantHighPrice, marketParticipantLowPrice, marketParticipantLastPrice, marketParticipantVolume }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 139 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, OriginalSaleCondition.encode_length, ConsolidatedPriceChangeIndicator.encode_length, MarketCenterOriginatorId.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, OriginalSaleCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, ConsolidatedPriceChangeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCenterOriginatorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Corrected Sale Condition: 4 bytes -/
structure CorrectedSaleCondition where
  level1 : Level1
  level2 : Level2
  level3 : Level3
  level4 : Alpha 1
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition

def encode (message : CorrectedSaleCondition) : List UInt8 :=
  Level1.encode message.level1
    ++ (Level2.encode message.level2
    ++ (Level3.encode message.level3
    ++ (Alpha.encode message.level4)))

def decode (bytes : List UInt8) : Option (CorrectedSaleCondition × List UInt8) := do
  let (level1, bytes) ← Level1.decode bytes
  let (level2, bytes) ← Level2.decode bytes
  let (level3, bytes) ← Level3.decode bytes
  let (level4, bytes) ← Alpha.decode 1 bytes
  pure ({ level1, level2, level3, level4 }, bytes)

@[simp] theorem encode_length (message : CorrectedSaleCondition) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Level1.encode_length, Level2.encode_length, Level3.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CorrectedSaleCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedSaleCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Level1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Level3.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CorrectedSaleCondition

/-- Trade Correction Message: 165 bytes -/
structure TradeCorrectionMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  originalTradeId : BitVec 64
  originalTradePrice : BitVec 64
  originalVolume : BitVec 32
  originalSaleCondition : OriginalSaleCondition
  originalTradeThroughExemptFlag : Alpha 1
  originalSellersSaleDays : BitVec 16
  correctedTradeId : BitVec 64
  correctedTradePrice : BitVec 64
  correctedVolume : BitVec 32
  correctedSaleCondition : CorrectedSaleCondition
  correctedTradeThroughExemptFlag : Alpha 1
  correctedSellersSaleDays : BitVec 16
  consolidatedHighPrice : BitVec 64
  consolidatedLowPrice : BitVec 64
  consolidatedLastPrice : BitVec 64
  consolidatedVolume : BitVec 64
  consolidatedPriceChangeIndicator : ConsolidatedPriceChangeIndicator
  marketCenterOriginatorId : MarketCenterOriginatorId
  marketParticipantHighPrice : BitVec 64
  marketParticipantLowPrice : BitVec 64
  marketParticipantLastPrice : BitVec 64
  marketParticipantVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.originalTradeId
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalVolume
    ++ (OriginalSaleCondition.encode message.originalSaleCondition
    ++ (Alpha.encode message.originalTradeThroughExemptFlag
    ++ (encodeUInt 2 message.originalSellersSaleDays
    ++ (encodeUInt 8 message.correctedTradeId
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedVolume
    ++ (CorrectedSaleCondition.encode message.correctedSaleCondition
    ++ (Alpha.encode message.correctedTradeThroughExemptFlag
    ++ (encodeUInt 2 message.correctedSellersSaleDays
    ++ (encodeUInt 8 message.consolidatedHighPrice
    ++ (encodeUInt 8 message.consolidatedLowPrice
    ++ (encodeUInt 8 message.consolidatedLastPrice
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (ConsolidatedPriceChangeIndicator.encode message.consolidatedPriceChangeIndicator
    ++ (MarketCenterOriginatorId.encode message.marketCenterOriginatorId
    ++ (encodeUInt 8 message.marketParticipantHighPrice
    ++ (encodeUInt 8 message.marketParticipantLowPrice
    ++ (encodeUInt 8 message.marketParticipantLastPrice
    ++ (encodeUInt 8 message.marketParticipantVolume))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (originalTradeId, bytes) ← decodeUInt 8 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (originalSaleCondition, bytes) ← OriginalSaleCondition.decode bytes
  let (originalTradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (originalSellersSaleDays, bytes) ← decodeUInt 2 bytes
  let (correctedTradeId, bytes) ← decodeUInt 8 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedVolume, bytes) ← decodeUInt 4 bytes
  let (correctedSaleCondition, bytes) ← CorrectedSaleCondition.decode bytes
  let (correctedTradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (correctedSellersSaleDays, bytes) ← decodeUInt 2 bytes
  let (consolidatedHighPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedLowPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedLastPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (consolidatedPriceChangeIndicator, bytes) ← ConsolidatedPriceChangeIndicator.decode bytes
  let (marketCenterOriginatorId, bytes) ← MarketCenterOriginatorId.decode bytes
  let (marketParticipantHighPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantLowPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantLastPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantVolume, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, originalTradeId, originalTradePrice, originalVolume, originalSaleCondition, originalTradeThroughExemptFlag, originalSellersSaleDays, correctedTradeId, correctedTradePrice, correctedVolume, correctedSaleCondition, correctedTradeThroughExemptFlag, correctedSellersSaleDays, consolidatedHighPrice, consolidatedLowPrice, consolidatedLastPrice, consolidatedVolume, consolidatedPriceChangeIndicator, marketCenterOriginatorId, marketParticipantHighPrice, marketParticipantLowPrice, marketParticipantLastPrice, marketParticipantVolume }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 165 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, OriginalSaleCondition.encode_length, CorrectedSaleCondition.encode_length, ConsolidatedPriceChangeIndicator.encode_length, MarketCenterOriginatorId.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, OriginalSaleCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, CorrectedSaleCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, ConsolidatedPriceChangeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCenterOriginatorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- Prior Day As Of Trade Message: 81 bytes -/
structure PriorDayAsOfTradeMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 64
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  saleCondition : SaleCondition
  tradeThroughExemptFlag : Alpha 1
  sellersSaleDays : BitVec 16
  asOfAction : AsOfAction
  timestampOfTrade : BitVec 64
  deriving DecidableEq, Repr

namespace PriorDayAsOfTradeMessage

def encode (message : PriorDayAsOfTradeMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (SaleCondition.encode message.saleCondition
    ++ (Alpha.encode message.tradeThroughExemptFlag
    ++ (encodeUInt 2 message.sellersSaleDays
    ++ (AsOfAction.encode message.asOfAction
    ++ (encodeUInt 8 message.timestampOfTrade))))))))))

def decode (bytes : List UInt8) : Option (PriorDayAsOfTradeMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (saleCondition, bytes) ← SaleCondition.decode bytes
  let (tradeThroughExemptFlag, bytes) ← Alpha.decode 1 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 2 bytes
  let (asOfAction, bytes) ← AsOfAction.decode bytes
  let (timestampOfTrade, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, tradeId, tradePrice, tradeVolume, saleCondition, tradeThroughExemptFlag, sellersSaleDays, asOfAction, timestampOfTrade }, bytes)

@[simp] theorem encode_length (message : PriorDayAsOfTradeMessage) : (encode message).length = 81 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, SaleCondition.encode_length, AsOfAction.encode_length]

theorem encode_length_pos (message : PriorDayAsOfTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayAsOfTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, SaleCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AsOfAction.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriorDayAsOfTradeMessage

/-- Any Trade Message Payload, selected by Trade Message Type -/
inductive TradeMessagePayload where
  | tradeReportMessageShortFormMessage (message : TradeReportMessageShortFormMessage) -- "A" 0x41
  | tradeReportMessageLongFormMessage (message : TradeReportMessageLongFormMessage) -- "W" 0x57
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "Z" 0x5A
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "Y" 0x59
  | priorDayAsOfTradeMessage (message : PriorDayAsOfTradeMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace TradeMessagePayload

/-- The Trade Message Type each message is sent under -/
def tag : TradeMessagePayload → BitVec 8
  | .tradeReportMessageShortFormMessage _ => 65
  | .tradeReportMessageLongFormMessage _ => 87
  | .tradeCancelErrorMessage _ => 90
  | .tradeCorrectionMessage _ => 89
  | .priorDayAsOfTradeMessage _ => 72

def encode : TradeMessagePayload → List UInt8
  | .tradeReportMessageShortFormMessage message => TradeReportMessageShortFormMessage.encode message
  | .tradeReportMessageLongFormMessage message => TradeReportMessageLongFormMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .priorDayAsOfTradeMessage message => PriorDayAsOfTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : TradeMessagePayload) : (encode message).length ≤ 165 := by
  cases message with
  | tradeReportMessageShortFormMessage inner =>
    simp only [encode, TradeReportMessageShortFormMessage.encode_length]
    omega
  | tradeReportMessageLongFormMessage inner =>
    simp only [encode, TradeReportMessageLongFormMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | priorDayAsOfTradeMessage inner =>
    simp only [encode, PriorDayAsOfTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (TradeMessagePayload × List UInt8) :=
  if tag = 65 then (TradeReportMessageShortFormMessage.decode bytes).map fun (message, rest) => (.tradeReportMessageShortFormMessage message, rest)
  else if tag = 87 then (TradeReportMessageLongFormMessage.decode bytes).map fun (message, rest) => (.tradeReportMessageLongFormMessage message, rest)
  else if tag = 90 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else if tag = 89 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 72 then (PriorDayAsOfTradeMessage.decode bytes).map fun (message, rest) => (.priorDayAsOfTradeMessage message, rest)
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
theorem encode_length_le (message : TradeMessage) : (encode message).length ≤ 166 := by
  unfold encode
  cases message.tradeMessagePayload with
  | tradeReportMessageShortFormMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeReportMessageShortFormMessage.encode_length]
    omega
  | tradeReportMessageLongFormMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeReportMessageLongFormMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | priorDayAsOfTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayAsOfTradeMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeMessagePayload.decode_encode, some_bind]
  rfl

end TradeMessage

/-- General Administrative Message -/
structure GeneralAdministrativeMessage where
  messageInfo : MessageInfo
  text : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace GeneralAdministrativeMessage

def encode (message : GeneralAdministrativeMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.text.val.length)
    ++ (encodeMany Byte.encode message.text.val))

def decode (bytes : List UInt8) : Option (GeneralAdministrativeMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (textLength, bytes) ← decodeUInt 2 bytes
  let (text_, bytes) ← decodeMany Byte.decode textLength.toNat bytes
  if fits_text : text_.length < 256 ^ 2 then
    pure ({ messageInfo, text := ⟨text_, fits_text⟩ }, bytes)
  else none

theorem encode_length_pos (message : GeneralAdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GeneralAdministrativeMessage) : (encode message).length ≤ 65563 := by
  have bound_text := message.text.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : GeneralAdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.text.length_lt]
  rfl

end GeneralAdministrativeMessage

/-- Cross Sro Trading Action Message: 56 bytes -/
structure CrossSroTradingActionMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionCode : TradingActionCode
  tradingActionSequenceNumber : BitVec 32
  actionTimestamp : BitVec 64
  tradingActionReason : Alpha 6
  deriving DecidableEq, Repr

namespace CrossSroTradingActionMessage

def encode (message : CrossSroTradingActionMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (TradingActionCode.encode message.tradingActionCode
    ++ (encodeUInt 4 message.tradingActionSequenceNumber
    ++ (encodeUInt 8 message.actionTimestamp
    ++ (Alpha.encode message.tradingActionReason)))))

def decode (bytes : List UInt8) : Option (CrossSroTradingActionMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionCode, bytes) ← TradingActionCode.decode bytes
  let (tradingActionSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (actionTimestamp, bytes) ← decodeUInt 8 bytes
  let (tradingActionReason, bytes) ← Alpha.decode 6 bytes
  pure ({ messageInfo, symbolLong, tradingActionCode, tradingActionSequenceNumber, actionTimestamp, tradingActionReason }, bytes)

@[simp] theorem encode_length (message : CrossSroTradingActionMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, TradingActionCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CrossSroTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossSroTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingActionCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossSroTradingActionMessage

/-- Market Center Trading Action Message: 47 bytes -/
structure MarketCenterTradingActionMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionCode : TradingActionCode
  actionTimestamp : BitVec 64
  marketCenterIdentifier : Alpha 1
  deriving DecidableEq, Repr

namespace MarketCenterTradingActionMessage

def encode (message : MarketCenterTradingActionMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (TradingActionCode.encode message.tradingActionCode
    ++ (encodeUInt 8 message.actionTimestamp
    ++ (Alpha.encode message.marketCenterIdentifier))))

def decode (bytes : List UInt8) : Option (MarketCenterTradingActionMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionCode, bytes) ← TradingActionCode.decode bytes
  let (actionTimestamp, bytes) ← decodeUInt 8 bytes
  let (marketCenterIdentifier, bytes) ← Alpha.decode 1 bytes
  pure ({ messageInfo, symbolLong, tradingActionCode, actionTimestamp, marketCenterIdentifier }, bytes)

@[simp] theorem encode_length (message : MarketCenterTradingActionMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, TradingActionCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketCenterTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingActionCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketCenterTradingActionMessage

/-- Issue Symbol Directory Message: 87 bytes -/
structure IssueSymbolDirectoryMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  oldSymbol : Alpha 11
  issueName : Alpha 30
  issueType : IssueType
  issueSubtype : Alpha 2
  marketTier : MarketTier
  authenticity : Authenticity
  shortSaleThresholdIndicator : ShortSaleThresholdIndicator
  roundLotSize : BitVec 16
  financialStatusIndicator : FinancialStatusIndicator
  deriving DecidableEq, Repr

namespace IssueSymbolDirectoryMessage

def encode (message : IssueSymbolDirectoryMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (Alpha.encode message.oldSymbol
    ++ (Alpha.encode message.issueName
    ++ (IssueType.encode message.issueType
    ++ (Alpha.encode message.issueSubtype
    ++ (MarketTier.encode message.marketTier
    ++ (Authenticity.encode message.authenticity
    ++ (ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ (encodeUInt 2 message.roundLotSize
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator))))))))))

def decode (bytes : List UInt8) : Option (IssueSymbolDirectoryMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (oldSymbol, bytes) ← Alpha.decode 11 bytes
  let (issueName, bytes) ← Alpha.decode 30 bytes
  let (issueType, bytes) ← IssueType.decode bytes
  let (issueSubtype, bytes) ← Alpha.decode 2 bytes
  let (marketTier, bytes) ← MarketTier.decode bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  let (shortSaleThresholdIndicator, bytes) ← ShortSaleThresholdIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 2 bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  pure ({ messageInfo, symbolLong, oldSymbol, issueName, issueType, issueSubtype, marketTier, authenticity, shortSaleThresholdIndicator, roundLotSize, financialStatusIndicator }, bytes)

@[simp] theorem encode_length (message : IssueSymbolDirectoryMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, IssueType.encode_length, MarketTier.encode_length, Authenticity.encode_length, ShortSaleThresholdIndicator.encode_length, encodeUInt_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : IssueSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueSymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IssueType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Authenticity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleThresholdIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [FinancialStatusIndicator.decode_encode, some_bind]
  rfl

end IssueSymbolDirectoryMessage

/-- Regulation Sho Short Sale Price Test Restricted Indicator Message: 32 bytes -/
structure RegulationShoShortSalePriceTestRestrictedIndicatorMessage where
  messageInfo : MessageInfo
  symbolShort : Alpha 5
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegulationShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolShort
    ++ (RegShoAction.encode message.regShoAction))

def decode (bytes : List UInt8) : Option (RegulationShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ messageInfo, symbolShort, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegulationShoShortSalePriceTestRestrictedIndicatorMessage

/-- Limit Up Limit Down Price Band Message: 62 bytes -/
structure LimitUpLimitDownPriceBandMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  luldPriceBandIndicator : LuldPriceBandIndicator
  luldTimestamp : BitVec 64
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  deriving DecidableEq, Repr

namespace LimitUpLimitDownPriceBandMessage

def encode (message : LimitUpLimitDownPriceBandMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (LuldPriceBandIndicator.encode message.luldPriceBandIndicator
    ++ (encodeUInt 8 message.luldTimestamp
    ++ (encodeUInt 8 message.limitDownPrice
    ++ (encodeUInt 8 message.limitUpPrice)))))

def decode (bytes : List UInt8) : Option (LimitUpLimitDownPriceBandMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (luldPriceBandIndicator, bytes) ← LuldPriceBandIndicator.decode bytes
  let (luldTimestamp, bytes) ← decodeUInt 8 bytes
  let (limitDownPrice, bytes) ← decodeUInt 8 bytes
  let (limitUpPrice, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, symbolLong, luldPriceBandIndicator, luldTimestamp, limitDownPrice, limitUpPrice }, bytes)

@[simp] theorem encode_length (message : LimitUpLimitDownPriceBandMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, LuldPriceBandIndicator.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LimitUpLimitDownPriceBandMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LimitUpLimitDownPriceBandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldPriceBandIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LimitUpLimitDownPriceBandMessage

/-- Market Wide Circuit Breaker Decline Level Message: 50 bytes -/
structure MarketWideCircuitBreakerDeclineLevelMessage where
  messageInfo : MessageInfo
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3)))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, mwcbLevel1, mwcbLevel2, mwcbLevel3 }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketWideCircuitBreakerDeclineLevelMessage

/-- Market Wide Circuit Breaker Status Message: 27 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  messageInfo : MessageInfo
  mwcbStatusLevelIndicator : MwcbStatusLevelIndicator
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (MwcbStatusLevelIndicator.encode message.mwcbStatusLevelIndicator)

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (mwcbStatusLevelIndicator, bytes) ← MwcbStatusLevelIndicator.decode bytes
  pure ({ messageInfo, mwcbStatusLevelIndicator }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, MwcbStatusLevelIndicator.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [MwcbStatusLevelIndicator.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Auction Collar Message: 66 bytes -/
structure AuctionCollarMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionSequenceNumber : BitVec 32
  collarReferencePrice : BitVec 64
  collarUpPrice : BitVec 64
  collarDownPrice : BitVec 64
  collarExtensionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionCollarMessage

def encode (message : AuctionCollarMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradingActionSequenceNumber
    ++ (encodeUInt 8 message.collarReferencePrice
    ++ (encodeUInt 8 message.collarUpPrice
    ++ (encodeUInt 8 message.collarDownPrice
    ++ (Alpha.encode message.collarExtensionIndicator))))))

def decode (bytes : List UInt8) : Option (AuctionCollarMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (collarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (collarUpPrice, bytes) ← decodeUInt 8 bytes
  let (collarDownPrice, bytes) ← decodeUInt 8 bytes
  let (collarExtensionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ messageInfo, symbolLong, tradingActionSequenceNumber, collarReferencePrice, collarUpPrice, collarDownPrice, collarExtensionIndicator }, bytes)

@[simp] theorem encode_length (message : AuctionCollarMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionCollarMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionCollarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionCollarMessage

/-- Market Center Closing Price And Volume Summary: 34 bytes -/
structure MarketCenterClosingPriceAndVolumeSummary where
  marketCenterIdentifier : Alpha 1
  marketCenterClosingPrice : BitVec 64
  marketCenterVolume : BitVec 64
  marketCenterCloseIndicator : MarketCenterCloseIndicator
  marketParticipantHighPrice : BitVec 64
  marketParticipantLowPrice : BitVec 64
  deriving DecidableEq, Repr

namespace MarketCenterClosingPriceAndVolumeSummary

def encode (message : MarketCenterClosingPriceAndVolumeSummary) : List UInt8 :=
  Alpha.encode message.marketCenterIdentifier
    ++ (encodeUInt 8 message.marketCenterClosingPrice
    ++ (encodeUInt 8 message.marketCenterVolume
    ++ (MarketCenterCloseIndicator.encode message.marketCenterCloseIndicator
    ++ (encodeUInt 8 message.marketParticipantHighPrice
    ++ (encodeUInt 8 message.marketParticipantLowPrice)))))

def decode (bytes : List UInt8) : Option (MarketCenterClosingPriceAndVolumeSummary × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← Alpha.decode 1 bytes
  let (marketCenterClosingPrice, bytes) ← decodeUInt 8 bytes
  let (marketCenterVolume, bytes) ← decodeUInt 8 bytes
  let (marketCenterCloseIndicator, bytes) ← MarketCenterCloseIndicator.decode bytes
  let (marketParticipantHighPrice, bytes) ← decodeUInt 8 bytes
  let (marketParticipantLowPrice, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenterIdentifier, marketCenterClosingPrice, marketCenterVolume, marketCenterCloseIndicator, marketParticipantHighPrice, marketParticipantLowPrice }, bytes)

@[simp] theorem encode_length (message : MarketCenterClosingPriceAndVolumeSummary) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, MarketCenterCloseIndicator.encode_length]

theorem encode_length_pos (message : MarketCenterClosingPriceAndVolumeSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterClosingPriceAndVolumeSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCenterCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketCenterClosingPriceAndVolumeSummary

/-- Closing Trade Summary Report Message -/
structure ClosingTradeSummaryReportMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  dailyConsolidatedHighPrice : BitVec 64
  dailyConsolidatedLowPrice : BitVec 64
  dailyConsolidatedClosingPrice : BitVec 64
  marketCenterOriginatorId : MarketCenterOriginatorId
  consolidatedVolume : BitVec 64
  tradingActionIndicator : TradingActionIndicator
  marketCenterClosingPriceAndVolumeSummary : Bounded 2 MarketCenterClosingPriceAndVolumeSummary
  deriving DecidableEq, Repr

namespace ClosingTradeSummaryReportMessage

def encode (message : ClosingTradeSummaryReportMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.dailyConsolidatedHighPrice
    ++ (encodeUInt 8 message.dailyConsolidatedLowPrice
    ++ (encodeUInt 8 message.dailyConsolidatedClosingPrice
    ++ (MarketCenterOriginatorId.encode message.marketCenterOriginatorId
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (TradingActionIndicator.encode message.tradingActionIndicator
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.marketCenterClosingPriceAndVolumeSummary.val.length)
    ++ (encodeMany MarketCenterClosingPriceAndVolumeSummary.encode message.marketCenterClosingPriceAndVolumeSummary.val)))))))))

def decode (bytes : List UInt8) : Option (ClosingTradeSummaryReportMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (dailyConsolidatedHighPrice, bytes) ← decodeUInt 8 bytes
  let (dailyConsolidatedLowPrice, bytes) ← decodeUInt 8 bytes
  let (dailyConsolidatedClosingPrice, bytes) ← decodeUInt 8 bytes
  let (marketCenterOriginatorId, bytes) ← MarketCenterOriginatorId.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (tradingActionIndicator, bytes) ← TradingActionIndicator.decode bytes
  let (numberOfMarketCenterSummaries, bytes) ← decodeUInt 2 bytes
  let (marketCenterClosingPriceAndVolumeSummary_, bytes) ← decodeMany MarketCenterClosingPriceAndVolumeSummary.decode numberOfMarketCenterSummaries.toNat bytes
  if fits_marketCenterClosingPriceAndVolumeSummary : marketCenterClosingPriceAndVolumeSummary_.length < 256 ^ 2 then
    pure ({ messageInfo, symbolLong, dailyConsolidatedHighPrice, dailyConsolidatedLowPrice, dailyConsolidatedClosingPrice, marketCenterOriginatorId, consolidatedVolume, tradingActionIndicator, marketCenterClosingPriceAndVolumeSummary := ⟨marketCenterClosingPriceAndVolumeSummary_, fits_marketCenterClosingPriceAndVolumeSummary⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClosingTradeSummaryReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClosingTradeSummaryReportMessage) : (encode message).length ≤ 2228263 := by
  have bound_marketCenterClosingPriceAndVolumeSummary := message.marketCenterClosingPriceAndVolumeSummary.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, MarketCenterOriginatorId.encode_length, TradingActionIndicator.encode_length, encodeMany_length_const MarketCenterClosingPriceAndVolumeSummary.encode 34 MarketCenterClosingPriceAndVolumeSummary.encode_length]
  omega

@[simp] theorem decode_encode (message : ClosingTradeSummaryReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCenterOriginatorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingActionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MarketCenterClosingPriceAndVolumeSummary.encode MarketCenterClosingPriceAndVolumeSummary.decode MarketCenterClosingPriceAndVolumeSummary.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketCenterClosingPriceAndVolumeSummary.length_lt]
  rfl

end ClosingTradeSummaryReportMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | generalAdministrativeMessage (message : GeneralAdministrativeMessage) -- "A" 0x41
  | crossSroTradingActionMessage (message : CrossSroTradingActionMessage) -- "H" 0x48
  | marketCenterTradingActionMessage (message : MarketCenterTradingActionMessage) -- "K" 0x4B
  | issueSymbolDirectoryMessage (message : IssueSymbolDirectoryMessage) -- "B" 0x42
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) -- "V" 0x56
  | limitUpLimitDownPriceBandMessage (message : LimitUpLimitDownPriceBandMessage) -- "P" 0x50
  | marketWideCircuitBreakerDeclineLevelMessage (message : MarketWideCircuitBreakerDeclineLevelMessage) -- "C" 0x43
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- "D" 0x44
  | auctionCollarMessage (message : AuctionCollarMessage) -- "E" 0x45
  | closingTradeSummaryReportMessage (message : ClosingTradeSummaryReportMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .generalAdministrativeMessage _ => 65
  | .crossSroTradingActionMessage _ => 72
  | .marketCenterTradingActionMessage _ => 75
  | .issueSymbolDirectoryMessage _ => 66
  | .regulationShoShortSalePriceTestRestrictedIndicatorMessage _ => 86
  | .limitUpLimitDownPriceBandMessage _ => 80
  | .marketWideCircuitBreakerDeclineLevelMessage _ => 67
  | .marketWideCircuitBreakerStatusMessage _ => 68
  | .auctionCollarMessage _ => 69
  | .closingTradeSummaryReportMessage _ => 90

def encode : AdministrativeMessagePayload → List UInt8
  | .generalAdministrativeMessage message => GeneralAdministrativeMessage.encode message
  | .crossSroTradingActionMessage message => CrossSroTradingActionMessage.encode message
  | .marketCenterTradingActionMessage message => MarketCenterTradingActionMessage.encode message
  | .issueSymbolDirectoryMessage message => IssueSymbolDirectoryMessage.encode message
  | .regulationShoShortSalePriceTestRestrictedIndicatorMessage message => RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .limitUpLimitDownPriceBandMessage message => LimitUpLimitDownPriceBandMessage.encode message
  | .marketWideCircuitBreakerDeclineLevelMessage message => MarketWideCircuitBreakerDeclineLevelMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message
  | .auctionCollarMessage message => AuctionCollarMessage.encode message
  | .closingTradeSummaryReportMessage message => ClosingTradeSummaryReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 2228263 := by
  cases message with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | crossSroTradingActionMessage inner =>
    simp only [encode, CrossSroTradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [encode, MarketCenterTradingActionMessage.encode_length]
    omega
  | issueSymbolDirectoryMessage inner =>
    simp only [encode, IssueSymbolDirectoryMessage.encode_length]
    omega
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | limitUpLimitDownPriceBandMessage inner =>
    simp only [encode, LimitUpLimitDownPriceBandMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [encode, AuctionCollarMessage.encode_length]
    omega
  | closingTradeSummaryReportMessage inner =>
    have bound_inner := ClosingTradeSummaryReportMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 65 then (GeneralAdministrativeMessage.decode bytes).map fun (message, rest) => (.generalAdministrativeMessage message, rest)
  else if tag = 72 then (CrossSroTradingActionMessage.decode bytes).map fun (message, rest) => (.crossSroTradingActionMessage message, rest)
  else if tag = 75 then (MarketCenterTradingActionMessage.decode bytes).map fun (message, rest) => (.marketCenterTradingActionMessage message, rest)
  else if tag = 66 then (IssueSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.issueSymbolDirectoryMessage message, rest)
  else if tag = 86 then (RegulationShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regulationShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 80 then (LimitUpLimitDownPriceBandMessage.decode bytes).map fun (message, rest) => (.limitUpLimitDownPriceBandMessage message, rest)
  else if tag = 67 then (MarketWideCircuitBreakerDeclineLevelMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelMessage message, rest)
  else if tag = 68 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
  else if tag = 69 then (AuctionCollarMessage.decode bytes).map fun (message, rest) => (.auctionCollarMessage message, rest)
  else if tag = 90 then (ClosingTradeSummaryReportMessage.decode bytes).map fun (message, rest) => (.closingTradeSummaryReportMessage message, rest)
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
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 2228264 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | crossSroTradingActionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, CrossSroTradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketCenterTradingActionMessage.encode_length]
    omega
  | issueSymbolDirectoryMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, IssueSymbolDirectoryMessage.encode_length]
    omega
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | limitUpLimitDownPriceBandMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, LimitUpLimitDownPriceBandMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, AuctionCollarMessage.encode_length]
    omega
  | closingTradeSummaryReportMessage inner =>
    have bound_inner := ClosingTradeSummaryReportMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Market Center Volume Attachment: 9 bytes -/
structure MarketCenterVolumeAttachment where
  marketCenterIdentifier : Alpha 1
  currentMarketCenterVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MarketCenterVolumeAttachment

def encode (message : MarketCenterVolumeAttachment) : List UInt8 :=
  Alpha.encode message.marketCenterIdentifier
    ++ (encodeUInt 8 message.currentMarketCenterVolume)

def decode (bytes : List UInt8) : Option (MarketCenterVolumeAttachment × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← Alpha.decode 1 bytes
  let (currentMarketCenterVolume, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenterIdentifier, currentMarketCenterVolume }, bytes)

@[simp] theorem encode_length (message : MarketCenterVolumeAttachment) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketCenterVolumeAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterVolumeAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketCenterVolumeAttachment

/-- Total Consolidated And Market Center Volume Message -/
structure TotalConsolidatedAndMarketCenterVolumeMessage where
  messageInfo : MessageInfo
  totalConsolidatedVolume : BitVec 64
  marketCenterVolumeAttachment : Bounded 2 MarketCenterVolumeAttachment
  deriving DecidableEq, Repr

namespace TotalConsolidatedAndMarketCenterVolumeMessage

def encode (message : TotalConsolidatedAndMarketCenterVolumeMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.totalConsolidatedVolume
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.marketCenterVolumeAttachment.val.length)
    ++ (encodeMany MarketCenterVolumeAttachment.encode message.marketCenterVolumeAttachment.val)))

def decode (bytes : List UInt8) : Option (TotalConsolidatedAndMarketCenterVolumeMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (totalConsolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (numberOfMarketCenterVolumes, bytes) ← decodeUInt 2 bytes
  let (marketCenterVolumeAttachment_, bytes) ← decodeMany MarketCenterVolumeAttachment.decode numberOfMarketCenterVolumes.toNat bytes
  if fits_marketCenterVolumeAttachment : marketCenterVolumeAttachment_.length < 256 ^ 2 then
    pure ({ messageInfo, totalConsolidatedVolume, marketCenterVolumeAttachment := ⟨marketCenterVolumeAttachment_, fits_marketCenterVolumeAttachment⟩ }, bytes)
  else none

theorem encode_length_pos (message : TotalConsolidatedAndMarketCenterVolumeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TotalConsolidatedAndMarketCenterVolumeMessage) : (encode message).length ≤ 589851 := by
  have bound_marketCenterVolumeAttachment := message.marketCenterVolumeAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, encodeMany_length_const MarketCenterVolumeAttachment.encode 9 MarketCenterVolumeAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : TotalConsolidatedAndMarketCenterVolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MarketCenterVolumeAttachment.encode MarketCenterVolumeAttachment.decode MarketCenterVolumeAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketCenterVolumeAttachment.length_lt]
  rfl

end TotalConsolidatedAndMarketCenterVolumeMessage

/-- Any Volume Message Payload, selected by Volume Message Type -/
inductive VolumeMessagePayload where
  | totalConsolidatedAndMarketCenterVolumeMessage (message : TotalConsolidatedAndMarketCenterVolumeMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace VolumeMessagePayload

/-- The Volume Message Type each message is sent under -/
def tag : VolumeMessagePayload → BitVec 8
  | .totalConsolidatedAndMarketCenterVolumeMessage _ => 77

def encode : VolumeMessagePayload → List UInt8
  | .totalConsolidatedAndMarketCenterVolumeMessage message => TotalConsolidatedAndMarketCenterVolumeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : VolumeMessagePayload) : (encode message).length ≤ 589851 := by
  cases message with
  | totalConsolidatedAndMarketCenterVolumeMessage inner =>
    have bound_inner := TotalConsolidatedAndMarketCenterVolumeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (VolumeMessagePayload × List UInt8) :=
  if tag = 77 then (TotalConsolidatedAndMarketCenterVolumeMessage.decode bytes).map fun (message, rest) => (.totalConsolidatedAndMarketCenterVolumeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : VolumeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end VolumeMessagePayload

/-- Volume Message -/
structure VolumeMessage where
  volumeMessagePayload : VolumeMessagePayload
  deriving DecidableEq, Repr

namespace VolumeMessage

def encode (message : VolumeMessage) : List UInt8 :=
  encodeUInt 1 (VolumeMessagePayload.tag message.volumeMessagePayload)
    ++ (VolumeMessagePayload.encode message.volumeMessagePayload)

def decode (bytes : List UInt8) : Option (VolumeMessage × List UInt8) := do
  let (volumeMessageType, bytes) ← decodeUInt 1 bytes
  let (volumeMessagePayload, bytes) ← VolumeMessagePayload.decode volumeMessageType bytes
  pure ({ volumeMessagePayload }, bytes)

theorem encode_length_pos (message : VolumeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : VolumeMessage) : (encode message).length ≤ 589852 := by
  unfold encode
  cases message.volumeMessagePayload with
  | totalConsolidatedAndMarketCenterVolumeMessage inner =>
    have bound_inner := TotalConsolidatedAndMarketCenterVolumeMessage.encode_length_le inner
    simp only [VolumeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : VolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [VolumeMessagePayload.decode_encode, some_bind]
  rfl

end VolumeMessage

/-- Start Of Day Message: 26 bytes -/
structure StartOfDayMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end StartOfDayMessage

/-- End Of Day Message: 26 bytes -/
structure EndOfDayMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfDayMessage

/-- Market Session Open Message: 26 bytes -/
structure MarketSessionOpenMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace MarketSessionOpenMessage

def encode (message : MarketSessionOpenMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (MarketSessionOpenMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : MarketSessionOpenMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : MarketSessionOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSessionOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end MarketSessionOpenMessage

/-- Market Session Close Message: 26 bytes -/
structure MarketSessionCloseMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace MarketSessionCloseMessage

def encode (message : MarketSessionCloseMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (MarketSessionCloseMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : MarketSessionCloseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : MarketSessionCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSessionCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end MarketSessionCloseMessage

/-- End Of Transmissions Message: 26 bytes -/
structure EndOfTransmissionsMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfTransmissionsMessage

def encode (message : EndOfTransmissionsMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfTransmissionsMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionsMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfTransmissionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfTransmissionsMessage

/-- End Of Trade Reporting Message: 26 bytes -/
structure EndOfTradeReportingMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfTradeReportingMessage

def encode (message : EndOfTradeReportingMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfTradeReportingMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfTradeReportingMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfTradeReportingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTradeReportingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfTradeReportingMessage

/-- End Of Consolidated Last Sale Eligibility: 26 bytes -/
structure EndOfConsolidatedLastSaleEligibility where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfConsolidatedLastSaleEligibility

def encode (message : EndOfConsolidatedLastSaleEligibility) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfConsolidatedLastSaleEligibility × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfConsolidatedLastSaleEligibility) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfConsolidatedLastSaleEligibility) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfConsolidatedLastSaleEligibility) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfConsolidatedLastSaleEligibility

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "I" 0x49
  | endOfDayMessage (message : EndOfDayMessage) -- "J" 0x4A
  | marketSessionOpenMessage (message : MarketSessionOpenMessage) -- "O" 0x4F
  | marketSessionCloseMessage (message : MarketSessionCloseMessage) -- "C" 0x43
  | endOfTransmissionsMessage (message : EndOfTransmissionsMessage) -- "Z" 0x5A
  | endOfTradeReportingMessage (message : EndOfTradeReportingMessage) -- "X" 0x58
  | endOfConsolidatedLastSaleEligibility (message : EndOfConsolidatedLastSaleEligibility) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 73
  | .endOfDayMessage _ => 74
  | .marketSessionOpenMessage _ => 79
  | .marketSessionCloseMessage _ => 67
  | .endOfTransmissionsMessage _ => 90
  | .endOfTradeReportingMessage _ => 88
  | .endOfConsolidatedLastSaleEligibility _ => 83

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .marketSessionOpenMessage message => MarketSessionOpenMessage.encode message
  | .marketSessionCloseMessage message => MarketSessionCloseMessage.encode message
  | .endOfTransmissionsMessage message => EndOfTransmissionsMessage.encode message
  | .endOfTradeReportingMessage message => EndOfTradeReportingMessage.encode message
  | .endOfConsolidatedLastSaleEligibility message => EndOfConsolidatedLastSaleEligibility.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 26 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | marketSessionOpenMessage inner =>
    simp only [encode, MarketSessionOpenMessage.encode_length]
    omega
  | marketSessionCloseMessage inner =>
    simp only [encode, MarketSessionCloseMessage.encode_length]
    omega
  | endOfTransmissionsMessage inner =>
    simp only [encode, EndOfTransmissionsMessage.encode_length]
    omega
  | endOfTradeReportingMessage inner =>
    simp only [encode, EndOfTradeReportingMessage.encode_length]
    omega
  | endOfConsolidatedLastSaleEligibility inner =>
    simp only [encode, EndOfConsolidatedLastSaleEligibility.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 73 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 74 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 79 then (MarketSessionOpenMessage.decode bytes).map fun (message, rest) => (.marketSessionOpenMessage message, rest)
  else if tag = 67 then (MarketSessionCloseMessage.decode bytes).map fun (message, rest) => (.marketSessionCloseMessage message, rest)
  else if tag = 90 then (EndOfTransmissionsMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionsMessage message, rest)
  else if tag = 88 then (EndOfTradeReportingMessage.decode bytes).map fun (message, rest) => (.endOfTradeReportingMessage message, rest)
  else if tag = 83 then (EndOfConsolidatedLastSaleEligibility.decode bytes).map fun (message, rest) => (.endOfConsolidatedLastSaleEligibility message, rest)
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
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 27 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega
  | marketSessionOpenMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, MarketSessionOpenMessage.encode_length]
    omega
  | marketSessionCloseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, MarketSessionCloseMessage.encode_length]
    omega
  | endOfTransmissionsMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfTransmissionsMessage.encode_length]
    omega
  | endOfTradeReportingMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfTradeReportingMessage.encode_length]
    omega
  | endOfConsolidatedLastSaleEligibility inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfConsolidatedLastSaleEligibility.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Any Payload, selected by Message Category -/
inductive Payload where
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | volumeMessage (message : VolumeMessage) -- "V" 0x56
  | controlMessage (message : ControlMessage) -- "C" 0x43
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Category each message is sent under -/
def tag : Payload → BitVec 8
  | .tradeMessage _ => 84
  | .administrativeMessage _ => 65
  | .volumeMessage _ => 86
  | .controlMessage _ => 67

def encode : Payload → List UInt8
  | .tradeMessage message => TradeMessage.encode message
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .volumeMessage message => VolumeMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 2228264 := by
  cases message with
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | volumeMessage inner =>
    have bound_inner := VolumeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 86 then (VolumeMessage.decode bytes).map fun (message, rest) => (.volumeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  version : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageCategory bytes
  pure ({ version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequence : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequence
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequence, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqUtdfOutputUtpV15
