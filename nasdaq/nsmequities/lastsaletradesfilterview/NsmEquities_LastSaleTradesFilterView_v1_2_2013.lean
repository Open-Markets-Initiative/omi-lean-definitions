import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale Trades FilterView v1.2.2013

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesLastsaletradesfilterviewAsciiitchV122013

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfTransmissions -- Start Of Transmissions
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfTransmissions -- End Of Transmissions
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfTransmissions => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfTransmissions => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfTransmissions
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfTransmissions

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfTransmissions => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfTransmissions => decide
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

/-- Market Center Identifier: one byte code -/
def MarketCenterIdentifier.codes : List UInt8 :=
  [0x51, 0x4C]

inductive MarketCenterIdentifier where
  | nasdaq -- Nasdaq
  | trf -- Trf
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenterIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenterIdentifier

def toByte : MarketCenterIdentifier → UInt8
  | .nasdaq => 0x51
  | .trf => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenterIdentifier :=
  if byte = 0x51 then .nasdaq
  else .trf

def ofByte (byte : UInt8) : MarketCenterIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenterIdentifier) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | trf => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenterIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenterIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenterIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenterIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenterIdentifier

/-- Security Class: one byte code -/
def SecurityClass.codes : List UInt8 :=
  [0x51, 0x4E, 0x41, 0x50, 0x5A]

inductive SecurityClass where
  | nasdaq -- Nasdaq
  | nyse -- Nyse
  | nyseMkt -- Nyse Mkt
  | nyseArca -- Nyse Arca
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityClass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityClass

def toByte : SecurityClass → UInt8
  | .nasdaq => 0x51
  | .nyse => 0x4E
  | .nyseMkt => 0x41
  | .nyseArca => 0x50
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityClass :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseMkt
  else if byte = 0x50 then .nyseArca
  else .bats

def ofByte (byte : UInt8) : SecurityClass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityClass) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | nyse => decide
  | nyseMkt => decide
  | nyseArca => decide
  | bats => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityClass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityClass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityClass) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityClass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityClass

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive SettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Trade Through Exemption: one byte code -/
def TradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x20]

inductive TradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeThroughExemption

def toByte : TradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else .notApplicable

def ofByte (byte : UInt8) : TradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeThroughExemption

/-- Extended Hours Or Sold Code: one byte code -/
def ExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive ExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLateOrOutOfSequence -- Extended Hours Trade Reported Late Or Out Of Sequence
  | soldLastReportedLateButInSequence -- Sold Last Reported Late But In Sequence
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExtendedHoursOrSoldCode

def toByte : ExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLateOrOutOfSequence => 0x55
  | .soldLastReportedLateButInSequence => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLateOrOutOfSequence
  else if byte = 0x4C then .soldLastReportedLateButInSequence
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : ExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLateOrOutOfSequence => decide
  | soldLastReportedLateButInSequence => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExtendedHoursOrSoldCode

/-- Special Sale Condition: one byte code -/
def SpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x57, 0x58, 0x6F, 0x20]

inductive SpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | officialClosePrice -- Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | officialOpeningPrice -- Official Opening Price
  | splitTrade -- Split Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialSaleCondition

def toByte : SpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .officialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .officialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .officialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .officialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else .notApplicable

def ofByte (byte : UInt8) : SpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | officialClosePrice => decide
  | priorReferencePrice => decide
  | officialOpeningPrice => decide
  | splitTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialSaleCondition

/-- Original Settlement Type: one byte code -/
def OriginalSettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive OriginalSettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSettlementType

def toByte : OriginalSettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : OriginalSettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSettlementType

/-- Original Trade Through Exemption: one byte code -/
def OriginalTradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x20]

inductive OriginalTradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalTradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalTradeThroughExemption

def toByte : OriginalTradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalTradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else .notApplicable

def ofByte (byte : UInt8) : OriginalTradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalTradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalTradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalTradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalTradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalTradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalTradeThroughExemption

/-- Original Extended Hours Or Sold Code: one byte code -/
def OriginalExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive OriginalExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLateOrOutOfSequence -- Extended Hours Trade Reported Late Or Out Of Sequence
  | soldLastReportedLateButInSequence -- Sold Last Reported Late But In Sequence
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalExtendedHoursOrSoldCode

def toByte : OriginalExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLateOrOutOfSequence => 0x55
  | .soldLastReportedLateButInSequence => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLateOrOutOfSequence
  else if byte = 0x4C then .soldLastReportedLateButInSequence
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : OriginalExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLateOrOutOfSequence => decide
  | soldLastReportedLateButInSequence => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalExtendedHoursOrSoldCode

/-- Original Special Sale Condition: one byte code -/
def OriginalSpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x57, 0x58, 0x6F, 0x20]

inductive OriginalSpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | officialClosePrice -- Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | officialOpeningPrice -- Official Opening Price
  | splitTrade -- Split Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSpecialSaleCondition

def toByte : OriginalSpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .officialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .officialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .officialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .officialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else .notApplicable

def ofByte (byte : UInt8) : OriginalSpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | officialClosePrice => decide
  | priorReferencePrice => decide
  | officialOpeningPrice => decide
  | splitTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSpecialSaleCondition

/-- Corrected Settlement Type: one byte code -/
def CorrectedSettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive CorrectedSettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSettlementType

def toByte : CorrectedSettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : CorrectedSettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSettlementType

/-- Corrected Trade Through Exemption: one byte code -/
def CorrectedTradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x20]

inductive CorrectedTradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedTradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedTradeThroughExemption

def toByte : CorrectedTradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedTradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedTradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedTradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedTradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedTradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedTradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedTradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedTradeThroughExemption

/-- Corrected Extended Hours Or Sold Code: one byte code -/
def CorrectedExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive CorrectedExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLateOrOutOfSequence -- Extended Hours Trade Reported Late Or Out Of Sequence
  | soldLastReportedLateButInSequence -- Sold Last Reported Late But In Sequence
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedExtendedHoursOrSoldCode

def toByte : CorrectedExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLateOrOutOfSequence => 0x55
  | .soldLastReportedLateButInSequence => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLateOrOutOfSequence
  else if byte = 0x4C then .soldLastReportedLateButInSequence
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLateOrOutOfSequence => decide
  | soldLastReportedLateButInSequence => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedExtendedHoursOrSoldCode

/-- Corrected Special Sale Condition: one byte code -/
def CorrectedSpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x57, 0x58, 0x6F, 0x20]

inductive CorrectedSpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | officialClosePrice -- Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | officialOpeningPrice -- Official Opening Price
  | splitTrade -- Split Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSpecialSaleCondition

def toByte : CorrectedSpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .officialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .officialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .officialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .officialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedSpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | officialClosePrice => decide
  | priorReferencePrice => decide
  | officialOpeningPrice => decide
  | splitTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSpecialSaleCondition

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive CurrentTradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quotationOnly
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quotationOnly => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentTradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentTradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentTradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentTradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentTradingState

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTest -- No Price Test
  | restrictionInEffect -- Restriction In Effect
  | restrictionRemains -- Restriction Remains
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .restrictionInEffect => 0x31
  | .restrictionRemains => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTest
  else if byte = 0x31 then .restrictionInEffect
  else .restrictionRemains

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTest => decide
  | restrictionInEffect => decide
  | restrictionRemains => decide
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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x4E, 0x41, 0x50, 0x51, 0x47, 0x53, 0x5A, 0x20]

inductive MarketCategory where
  | nyse -- Nyse
  | nyseMkt -- Nyse Mkt
  | nyseArca -- Nyse Arca
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | bats -- Bats
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nyse => 0x4E
  | .nyseMkt => 0x41
  | .nyseArca => 0x50
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .bats => 0x5A
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseMkt
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else if byte = 0x5A then .bats
  else .notAvailable

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | nyseMkt => decide
  | nyseArca => decide
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | bats => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCategory

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x4E, 0x44, 0x45, 0x51, 0x47, 0x48, 0x4A, 0x4B, 0x53, 0x20]

inductive FinancialStatusIndicator where
  | normal -- Normal
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | suspended -- Suspended
  | inComplianceOrNotListed -- In Compliance Or Not Listed
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .normal => 0x4E
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .suspended => 0x53
  | .inComplianceOrNotListed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x4E then .normal
  else if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else if byte = 0x4B then .deficientDelinquentAndBankrupt
  else if byte = 0x53 then .suspended
  else .inComplianceOrNotListed

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | suspended => decide
  | inComplianceOrNotListed => decide
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

/-- Sale Condition Modifier: 4 bytes -/
structure SaleConditionModifier where
  settlementType : SettlementType
  tradeThroughExemption : TradeThroughExemption
  extendedHoursOrSoldCode : ExtendedHoursOrSoldCode
  specialSaleCondition : SpecialSaleCondition
  deriving DecidableEq, Repr

namespace SaleConditionModifier

def encode (message : SaleConditionModifier) : List UInt8 :=
  SettlementType.encode message.settlementType
    ++ (TradeThroughExemption.encode message.tradeThroughExemption
    ++ (ExtendedHoursOrSoldCode.encode message.extendedHoursOrSoldCode
    ++ (SpecialSaleCondition.encode message.specialSaleCondition)))

def decode (bytes : List UInt8) : Option (SaleConditionModifier × List UInt8) := do
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (tradeThroughExemption, bytes) ← TradeThroughExemption.decode bytes
  let (extendedHoursOrSoldCode, bytes) ← ExtendedHoursOrSoldCode.decode bytes
  let (specialSaleCondition, bytes) ← SpecialSaleCondition.decode bytes
  pure ({ settlementType, tradeThroughExemption, extendedHoursOrSoldCode, specialSaleCondition }, bytes)

@[simp] theorem encode_length (message : SaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, SettlementType.encode_length, TradeThroughExemption.encode_length, ExtendedHoursOrSoldCode.encode_length, SpecialSaleCondition.encode_length]

theorem encode_length_pos (message : SaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [SpecialSaleCondition.decode_encode, some_bind]
  rfl

end SaleConditionModifier

/-- Trade Report Message: 43 bytes -/
structure TradeReportMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  tradePrice : Alpha 10
  tradeSize : Alpha 9
  saleConditionModifier : SaleConditionModifier
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradeSize
    ++ (SaleConditionModifier.encode message.saleConditionModifier))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradeSize, bytes) ← Alpha.decode 9 bytes
  let (saleConditionModifier, bytes) ← SaleConditionModifier.decode bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, tradeControlNumber, tradePrice, tradeSize, saleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, SaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SaleConditionModifier.decode_encode, some_bind]
  rfl

end TradeReportMessage

/-- Original Sale Condition Modifier: 4 bytes -/
structure OriginalSaleConditionModifier where
  originalSettlementType : OriginalSettlementType
  originalTradeThroughExemption : OriginalTradeThroughExemption
  originalExtendedHoursOrSoldCode : OriginalExtendedHoursOrSoldCode
  originalSpecialSaleCondition : OriginalSpecialSaleCondition
  deriving DecidableEq, Repr

namespace OriginalSaleConditionModifier

def encode (message : OriginalSaleConditionModifier) : List UInt8 :=
  OriginalSettlementType.encode message.originalSettlementType
    ++ (OriginalTradeThroughExemption.encode message.originalTradeThroughExemption
    ++ (OriginalExtendedHoursOrSoldCode.encode message.originalExtendedHoursOrSoldCode
    ++ (OriginalSpecialSaleCondition.encode message.originalSpecialSaleCondition)))

def decode (bytes : List UInt8) : Option (OriginalSaleConditionModifier × List UInt8) := do
  let (originalSettlementType, bytes) ← OriginalSettlementType.decode bytes
  let (originalTradeThroughExemption, bytes) ← OriginalTradeThroughExemption.decode bytes
  let (originalExtendedHoursOrSoldCode, bytes) ← OriginalExtendedHoursOrSoldCode.decode bytes
  let (originalSpecialSaleCondition, bytes) ← OriginalSpecialSaleCondition.decode bytes
  pure ({ originalSettlementType, originalTradeThroughExemption, originalExtendedHoursOrSoldCode, originalSpecialSaleCondition }, bytes)

@[simp] theorem encode_length (message : OriginalSaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, OriginalSettlementType.encode_length, OriginalTradeThroughExemption.encode_length, OriginalExtendedHoursOrSoldCode.encode_length, OriginalSpecialSaleCondition.encode_length]

theorem encode_length_pos (message : OriginalSaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalSaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginalSettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalTradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [OriginalSpecialSaleCondition.decode_encode, some_bind]
  rfl

end OriginalSaleConditionModifier

/-- Trade Cancel Error Message: 43 bytes -/
structure TradeCancelErrorMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : Alpha 10
  originalTradeSize : Alpha 9
  originalSaleConditionModifier : OriginalSaleConditionModifier
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (Alpha.encode message.originalTradePrice
    ++ (Alpha.encode message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← Alpha.decode 10 bytes
  let (originalTradeSize, bytes) ← Alpha.decode 9 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, OriginalSaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OriginalSaleConditionModifier.decode_encode, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Corrected Sale Condition Modifier: 4 bytes -/
structure CorrectedSaleConditionModifier where
  correctedSettlementType : CorrectedSettlementType
  correctedTradeThroughExemption : CorrectedTradeThroughExemption
  correctedExtendedHoursOrSoldCode : CorrectedExtendedHoursOrSoldCode
  correctedSpecialSaleCondition : CorrectedSpecialSaleCondition
  deriving DecidableEq, Repr

namespace CorrectedSaleConditionModifier

def encode (message : CorrectedSaleConditionModifier) : List UInt8 :=
  CorrectedSettlementType.encode message.correctedSettlementType
    ++ (CorrectedTradeThroughExemption.encode message.correctedTradeThroughExemption
    ++ (CorrectedExtendedHoursOrSoldCode.encode message.correctedExtendedHoursOrSoldCode
    ++ (CorrectedSpecialSaleCondition.encode message.correctedSpecialSaleCondition)))

def decode (bytes : List UInt8) : Option (CorrectedSaleConditionModifier × List UInt8) := do
  let (correctedSettlementType, bytes) ← CorrectedSettlementType.decode bytes
  let (correctedTradeThroughExemption, bytes) ← CorrectedTradeThroughExemption.decode bytes
  let (correctedExtendedHoursOrSoldCode, bytes) ← CorrectedExtendedHoursOrSoldCode.decode bytes
  let (correctedSpecialSaleCondition, bytes) ← CorrectedSpecialSaleCondition.decode bytes
  pure ({ correctedSettlementType, correctedTradeThroughExemption, correctedExtendedHoursOrSoldCode, correctedSpecialSaleCondition }, bytes)

@[simp] theorem encode_length (message : CorrectedSaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, CorrectedSettlementType.encode_length, CorrectedTradeThroughExemption.encode_length, CorrectedExtendedHoursOrSoldCode.encode_length, CorrectedSpecialSaleCondition.encode_length]

theorem encode_length_pos (message : CorrectedSaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedSaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, CorrectedSettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedTradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [CorrectedSpecialSaleCondition.decode_encode, some_bind]
  rfl

end CorrectedSaleConditionModifier

/-- Trade Correction Message: 76 bytes -/
structure TradeCorrectionMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : Alpha 10
  originalTradeSize : Alpha 9
  originalSaleConditionModifier : OriginalSaleConditionModifier
  correctedTradeControlNumber : Alpha 10
  correctedTradePrice : Alpha 10
  correctedTradeSize : Alpha 9
  correctedSaleConditionModifier : CorrectedSaleConditionModifier
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (Alpha.encode message.originalTradePrice
    ++ (Alpha.encode message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (Alpha.encode message.correctedTradePrice
    ++ (Alpha.encode message.correctedTradeSize
    ++ (CorrectedSaleConditionModifier.encode message.correctedSaleConditionModifier))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← Alpha.decode 10 bytes
  let (originalTradeSize, bytes) ← Alpha.decode 9 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedTradePrice, bytes) ← Alpha.decode 10 bytes
  let (correctedTradeSize, bytes) ← Alpha.decode 9 bytes
  let (correctedSaleConditionModifier, bytes) ← CorrectedSaleConditionModifier.decode bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedTradePrice, correctedTradeSize, correctedSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, OriginalSaleConditionModifier.encode_length, CorrectedSaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CorrectedSaleConditionModifier.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Stock Trading Action Message: 14 bytes -/
structure StockTradingActionMessage where
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  currentTradingState : CurrentTradingState
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (CurrentTradingState.encode message.currentTradingState
    ++ (Alpha.encode message.reason)))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ issueSymbol, securityClass, currentTradingState, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentTradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 9 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction)

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Stock Directory Message: 10 bytes -/
structure StockDirectoryMessage where
  issueSymbol : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  pure ({ issueSymbol, marketCategory, financialStatusIndicator }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
  dsimp only
  rw [FinancialStatusIndicator.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Adjusted Closing Price Message: 19 bytes -/
structure AdjustedClosingPriceMessage where
  stock : Alpha 8
  securityClass : SecurityClass
  adjustedClosingPrice : Alpha 10
  deriving DecidableEq, Repr

namespace AdjustedClosingPriceMessage

def encode (message : AdjustedClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.adjustedClosingPrice))

def decode (bytes : List UInt8) : Option (AdjustedClosingPriceMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (adjustedClosingPrice, bytes) ← Alpha.decode 10 bytes
  pure ({ stock, securityClass, adjustedClosingPrice }, bytes)

@[simp] theorem encode_length (message : AdjustedClosingPriceMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length]

theorem encode_length_pos (message : AdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdjustedClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AdjustedClosingPriceMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | tradeReportMessage (message : TradeReportMessage) -- "T" 0x54
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "X" 0x58
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "Y" 0x59
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | adjustedClosingPriceMessage (message : AdjustedClosingPriceMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .tradeReportMessage _ => 84
  | .tradeCancelErrorMessage _ => 88
  | .tradeCorrectionMessage _ => 67
  | .stockTradingActionMessage _ => 72
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .stockDirectoryMessage _ => 82
  | .adjustedClosingPriceMessage _ => 71

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .adjustedClosingPriceMessage message => AdjustedClosingPriceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 76 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [encode, AdjustedClosingPriceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 88 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 71 then (AdjustedClosingPriceMessage.decode bytes).map fun (message, rest) => (.adjustedClosingPriceMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  timestamp : Alpha 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ timestamp, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AdjustedClosingPriceMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 32
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNsmequitiesLastsaletradesfilterviewAsciiitchV122013
