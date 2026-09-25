import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Net Order Imbalance View v2.1.20130309

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesNoiviewItchV2120130309

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x58, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | clearNoiiOpeningCrossData -- Clear Noii Opening Cross Data
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .clearNoiiOpeningCrossData => 0x58
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x58 then .clearNoiiOpeningCrossData
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | clearNoiiOpeningCrossData => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x4E, 0x41, 0x50, 0x51, 0x47, 0x53, 0x5A]

inductive MarketCategory where
  | newYorkStockExchangeNyse -- New York Stock Exchange Nyse
  | nyseAmex -- Nyse Amex
  | nyseArca -- Nyse Arca
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | batsBzxExchange -- Bats Bzx Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .newYorkStockExchangeNyse => 0x4E
  | .nyseAmex => 0x41
  | .nyseArca => 0x50
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .batsBzxExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x4E then .newYorkStockExchangeNyse
  else if byte = 0x41 then .nyseAmex
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else .batsBzxExchange

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | newYorkStockExchangeNyse => decide
  | nyseAmex => decide
  | nyseArca => decide
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | batsBzxExchange => decide
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
  [0x44, 0x45, 0x51, 0x53, 0x47, 0x48, 0x4A, 0x4B, 0x20]

inductive FinancialStatusIndicator where
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | suspended -- Suspended
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | companyIsInCompliance -- Company Is In Compliance
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .suspended => 0x53
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .companyIsInCompliance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x53 then .suspended
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else if byte = 0x4B then .deficientDelinquentAndBankrupt
  else .companyIsInCompliance

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | suspended => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | companyIsInCompliance => decide
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

/-- Round Lots Only: one byte code -/
def RoundLotsOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLotsOnly where
  | onlyRoundLotsAreAcceptedInThisStock -- Only Round Lots Are Accepted In This Stock
  | oddmixedLotsAreAllowed -- Oddmixed Lots Are Allowed
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .onlyRoundLotsAreAcceptedInThisStock => 0x59
  | .oddmixedLotsAreAllowed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .onlyRoundLotsAreAcceptedInThisStock
  else .oddmixedLotsAreAllowed

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | onlyRoundLotsAreAcceptedInThisStock => decide
  | oddmixedLotsAreAllowed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLotsOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLotsOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLotsOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLotsOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLotsOnly

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive CurrentTradingState where
  | haltedOrPausedAcrossAllUsEquityMarketsSrOs -- Halted Or Paused Across All Us Equity Markets Sr Os
  | pausedAcrossAllUsEquityMarketsSrOs -- Paused Across All Us Equity Markets Sr Os
  | quotationOnlyPeriodForCrossSroHaltOrPause -- Quotation Only Period For Cross Sro Halt Or Pause
  | tradingOnNasdaq -- Trading On Nasdaq
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltedOrPausedAcrossAllUsEquityMarketsSrOs => 0x48
  | .pausedAcrossAllUsEquityMarketsSrOs => 0x50
  | .quotationOnlyPeriodForCrossSroHaltOrPause => 0x51
  | .tradingOnNasdaq => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltedOrPausedAcrossAllUsEquityMarketsSrOs
  else if byte = 0x50 then .pausedAcrossAllUsEquityMarketsSrOs
  else if byte = 0x51 then .quotationOnlyPeriodForCrossSroHaltOrPause
  else .tradingOnNasdaq

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltedOrPausedAcrossAllUsEquityMarketsSrOs => decide
  | pausedAcrossAllUsEquityMarketsSrOs => decide
  | quotationOnlyPeriodForCrossSroHaltOrPause => decide
  | tradingOnNasdaq => decide
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
  | noPriceTestInPlace -- No Price Test In Place
  | regShoShortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInSecurity -- Reg Sho Short Sale Price Test Restriction In Effect Due To An Intraday Price Drop In Security
  | regShoShortSalePriceTestRestrictionRemainsInEffect -- Reg Sho Short Sale Price Test Restriction Remains In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTestInPlace => 0x30
  | .regShoShortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInSecurity => 0x31
  | .regShoShortSalePriceTestRestrictionRemainsInEffect => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTestInPlace
  else if byte = 0x31 then .regShoShortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInSecurity
  else .regShoShortSalePriceTestRestrictionRemainsInEffect

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTestInPlace => decide
  | regShoShortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInSecurity => decide
  | regShoShortSalePriceTestRestrictionRemainsInEffect => decide
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

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x53, 0x4E, 0x4F]

inductive ImbalanceDirection where
  | buyImbalance -- Buy Imbalance
  | sellImbalance -- Sell Imbalance
  | noImbalance -- No Imbalance
  | insufficientOrdersToCalculate -- Insufficient Orders To Calculate
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buyImbalance => 0x42
  | .sellImbalance => 0x53
  | .noImbalance => 0x4E
  | .insufficientOrdersToCalculate => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buyImbalance
  else if byte = 0x53 then .sellImbalance
  else if byte = 0x4E then .noImbalance
  else .insufficientOrdersToCalculate

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyImbalance => decide
  | sellImbalance => decide
  | noImbalance => decide
  | insufficientOrdersToCalculate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceDirection

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x43, 0x48]

inductive CrossType where
  | openCross -- Open Cross
  | closeCross -- Close Cross
  | intradayOpeningCrossForIpoAndHaltedPausedSecurities -- Intraday Opening Cross For Ipo And Halted Paused Securities
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openCross => 0x4F
  | .closeCross => 0x43
  | .intradayOpeningCrossForIpoAndHaltedPausedSecurities => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openCross
  else if byte = 0x43 then .closeCross
  else .intradayOpeningCrossForIpoAndHaltedPausedSecurities

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openCross => decide
  | closeCross => decide
  | intradayOpeningCrossForIpoAndHaltedPausedSecurities => decide
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

/-- Price Variation Indicator: one byte code -/
def PriceVariationIndicator.codes : List UInt8 :=
  [0x4C, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x20]

inductive PriceVariationIndicator where
  | lessThan1 -- Less Than 1%
  | oneToOnePointNineNinePercent -- One To One Point Nine Nine Percent
  | twoToTwoPointNineNinePercent -- Two To Two Point Nine Nine Percent
  | threeToThreePointNineNinePercent -- Three To Three Point Nine Nine Percent
  | fourToFourPointNineNinePercent -- Four To Four Point Nine Nine Percent
  | fiveToFivePointNineNinePercent -- Five To Five Point Nine Nine Percent
  | sixToSixPointNineNinePercent -- Six To Six Point Nine Nine Percent
  | sevenToSevenPointNineNinePercent -- Seven To Seven Point Nine Nine Percent
  | eightToEightPointNineNinePercent -- Eight To Eight Point Nine Nine Percent
  | nineToNinePointNineNinePercent -- Nine To Nine Point Nine Nine Percent
  | tenToNineteenPointNineNinePercent -- Ten To Nineteen Point Nine Nine Percent
  | twentyToTwentyNinePointNineNinePercent -- Twenty To Twenty Nine Point Nine Nine Percent
  | thirtyPercentOrGreater -- Thirty Percent Or Greater
  | cannotBeCalculated -- Cannot Be Calculated
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceVariationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceVariationIndicator

def toByte : PriceVariationIndicator → UInt8
  | .lessThan1 => 0x4C
  | .oneToOnePointNineNinePercent => 0x31
  | .twoToTwoPointNineNinePercent => 0x32
  | .threeToThreePointNineNinePercent => 0x33
  | .fourToFourPointNineNinePercent => 0x34
  | .fiveToFivePointNineNinePercent => 0x35
  | .sixToSixPointNineNinePercent => 0x36
  | .sevenToSevenPointNineNinePercent => 0x37
  | .eightToEightPointNineNinePercent => 0x38
  | .nineToNinePointNineNinePercent => 0x39
  | .tenToNineteenPointNineNinePercent => 0x41
  | .twentyToTwentyNinePointNineNinePercent => 0x42
  | .thirtyPercentOrGreater => 0x43
  | .cannotBeCalculated => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceVariationIndicator :=
  if byte = 0x4C then .lessThan1
  else if byte = 0x31 then .oneToOnePointNineNinePercent
  else if byte = 0x32 then .twoToTwoPointNineNinePercent
  else if byte = 0x33 then .threeToThreePointNineNinePercent
  else if byte = 0x34 then .fourToFourPointNineNinePercent
  else if byte = 0x35 then .fiveToFivePointNineNinePercent
  else if byte = 0x36 then .sixToSixPointNineNinePercent
  else if byte = 0x37 then .sevenToSevenPointNineNinePercent
  else if byte = 0x38 then .eightToEightPointNineNinePercent
  else if byte = 0x39 then .nineToNinePointNineNinePercent
  else if byte = 0x41 then .tenToNineteenPointNineNinePercent
  else if byte = 0x42 then .twentyToTwentyNinePointNineNinePercent
  else if byte = 0x43 then .thirtyPercentOrGreater
  else .cannotBeCalculated

def ofByte (byte : UInt8) : PriceVariationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceVariationIndicator) : ofByte value.toByte = value := by
  cases value with
  | lessThan1 => decide
  | oneToOnePointNineNinePercent => decide
  | twoToTwoPointNineNinePercent => decide
  | threeToThreePointNineNinePercent => decide
  | fourToFourPointNineNinePercent => decide
  | fiveToFivePointNineNinePercent => decide
  | sixToSixPointNineNinePercent => decide
  | sevenToSevenPointNineNinePercent => decide
  | eightToEightPointNineNinePercent => decide
  | nineToNinePointNineNinePercent => decide
  | tenToNineteenPointNineNinePercent => decide
  | twentyToTwentyNinePointNineNinePercent => decide
  | thirtyPercentOrGreater => decide
  | cannotBeCalculated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceVariationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceVariationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceVariationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceVariationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceVariationIndicator

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

/-- Stock Directory Message: 17 bytes -/
structure StockDirectoryMessage where
  stock : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  roundLotSize : Alpha 6
  roundLotsOnly : RoundLotsOnly
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (Alpha.encode message.roundLotSize
    ++ (RoundLotsOnly.encode message.roundLotsOnly))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← Alpha.decode 6 bytes
  let (roundLotsOnly, bytes) ← RoundLotsOnly.decode bytes
  pure ({ stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length, RoundLotsOnly.encode_length]

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
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RoundLotsOnly.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Stock Trading Action Message: 13 bytes -/
structure StockTradingActionMessage where
  stock : Alpha 8
  currentTradingState : CurrentTradingState
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (CurrentTradingState.encode message.currentTradingState
    ++ (Alpha.encode message.reason))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ stock, currentTradingState, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentTradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Reg Sho Restriction Message: 9 bytes -/
structure RegShoRestrictionMessage where
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoRestrictionMessage

def encode (message : RegShoRestrictionMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction)

def decode (bytes : List UInt8) : Option (RegShoRestrictionMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoRestrictionMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoRestrictionMessage

/-- Noii Message: 59 bytes -/
structure NoiiMessage where
  pairedShares : Alpha 9
  imbalanceShares : Alpha 9
  imbalanceDirection : ImbalanceDirection
  stock : Alpha 8
  farPrice : Alpha 10
  nearPrice : Alpha 10
  currentReferencePrice : Alpha 10
  crossType : CrossType
  priceVariationIndicator : PriceVariationIndicator
  deriving DecidableEq, Repr

namespace NoiiMessage

def encode (message : NoiiMessage) : List UInt8 :=
  Alpha.encode message.pairedShares
    ++ (Alpha.encode message.imbalanceShares
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.farPrice
    ++ (Alpha.encode message.nearPrice
    ++ (Alpha.encode message.currentReferencePrice
    ++ (CrossType.encode message.crossType
    ++ (PriceVariationIndicator.encode message.priceVariationIndicator))))))))

def decode (bytes : List UInt8) : Option (NoiiMessage × List UInt8) := do
  let (pairedShares, bytes) ← Alpha.decode 9 bytes
  let (imbalanceShares, bytes) ← Alpha.decode 9 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (farPrice, bytes) ← Alpha.decode 10 bytes
  let (nearPrice, bytes) ← Alpha.decode 10 bytes
  let (currentReferencePrice, bytes) ← Alpha.decode 10 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceVariationIndicator, bytes) ← PriceVariationIndicator.decode bytes
  pure ({ pairedShares, imbalanceShares, imbalanceDirection, stock, farPrice, nearPrice, currentReferencePrice, crossType, priceVariationIndicator }, bytes)

@[simp] theorem encode_length (message : NoiiMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ImbalanceDirection.encode_length, CrossType.encode_length, PriceVariationIndicator.encode_length]

theorem encode_length_pos (message : NoiiMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NoiiMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [PriceVariationIndicator.decode_encode, some_bind]
  rfl

end NoiiMessage

/-- Cross Trade Message: 40 bytes -/
structure CrossTradeMessage where
  shares : Alpha 9
  stock : Alpha 8
  crossPrice : Alpha 10
  matchNumber : Alpha 12
  crossType : CrossType
  deriving DecidableEq, Repr

namespace CrossTradeMessage

def encode (message : CrossTradeMessage) : List UInt8 :=
  Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.crossPrice
    ++ (Alpha.encode message.matchNumber
    ++ (CrossType.encode message.crossType))))

def decode (bytes : List UInt8) : Option (CrossTradeMessage × List UInt8) := do
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (crossPrice, bytes) ← Alpha.decode 10 bytes
  let (matchNumber, bytes) ← Alpha.decode 12 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ shares, stock, crossPrice, matchNumber, crossType }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : CrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossTradeMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end CrossTradeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | regShoRestrictionMessage (message : RegShoRestrictionMessage) -- "Y" 0x59
  | noiiMessage (message : NoiiMessage) -- "I" 0x49
  | crossTradeMessage (message : CrossTradeMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockTradingActionMessage _ => 72
  | .regShoRestrictionMessage _ => 89
  | .noiiMessage _ => 73
  | .crossTradeMessage _ => 81

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .regShoRestrictionMessage message => RegShoRestrictionMessage.encode message
  | .noiiMessage message => NoiiMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 59 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [encode, RegShoRestrictionMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [encode, NoiiMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [encode, CrossTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 89 then (RegShoRestrictionMessage.decode bytes).map fun (message, rest) => (.regShoRestrictionMessage message, rest)
  else if tag = 73 then (NoiiMessage.decode bytes).map fun (message, rest) => (.noiiMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
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
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RegShoRestrictionMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NoiiMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, CrossTradeMessage.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
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
  sequence : BitVec 32
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 4 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequence, bytes) ← decodeUInt 4 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNsmequitiesNoiviewItchV2120130309
