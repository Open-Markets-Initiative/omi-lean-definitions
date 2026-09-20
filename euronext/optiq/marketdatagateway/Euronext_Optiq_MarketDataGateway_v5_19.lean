import Omi.Wire
import Std.Tactic.BVDecide

/-!
# Euronext Market Data Gateway v5.19

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Trade Qualifier is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Phase Qualifier is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Order Type Rules is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Mm Protections is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Strategy Authorized is a bit field set, proven as its 8 byte integer rather than bit by bit.

Note: Compression says whether the Optiq Message was LZ4 transformed: the bytes of a transformed body are carried as they lie rather than read, and Compression is written from which of the two the message holds.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EuronextOptiqMarketdatagatewaySbeV519

/-- Mmt Trading Mode: one byte code -/
def MmtTradingMode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x49, 0x4B, 0x4F, 0x55]

inductive MmtTradingMode where
  | undefinedAuctionequalUncrossing -- Undefined Auctionequal Uncrossing
  | continuousTrading -- Continuous Trading
  | atMarketCloseTrading -- At Market Close Trading
  | outofMainSessionTrading -- Outof Main Session Trading
  | tradeReportingOnExchange -- Trade Reporting On Exchange
  | tradeReportingOffExchange -- Trade Reporting Off Exchange
  | tradeReportingSystematicInternaliser -- Trade Reporting Systematic Internaliser
  | scheduledIntradayAuctionequalUncrossing -- Scheduled Intraday Auctionequal Uncrossing
  | scheduledClosingAuctionequalUncrossing -- Scheduled Closing Auctionequal Uncrossing
  | scheduledOpeningAuctionequalUncrossing -- Scheduled Opening Auctionequal Uncrossing
  | unscheduledAuctionequalUncrossing -- Unscheduled Auctionequal Uncrossing
  | unlisted (byte : { byte : UInt8 // byte ∉ MmtTradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MmtTradingMode

def toByte : MmtTradingMode → UInt8
  | .undefinedAuctionequalUncrossing => 0x31
  | .continuousTrading => 0x32
  | .atMarketCloseTrading => 0x33
  | .outofMainSessionTrading => 0x34
  | .tradeReportingOnExchange => 0x35
  | .tradeReportingOffExchange => 0x36
  | .tradeReportingSystematicInternaliser => 0x37
  | .scheduledIntradayAuctionequalUncrossing => 0x49
  | .scheduledClosingAuctionequalUncrossing => 0x4B
  | .scheduledOpeningAuctionequalUncrossing => 0x4F
  | .unscheduledAuctionequalUncrossing => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MmtTradingMode :=
  if byte = 0x31 then .undefinedAuctionequalUncrossing
  else if byte = 0x32 then .continuousTrading
  else if byte = 0x33 then .atMarketCloseTrading
  else if byte = 0x34 then .outofMainSessionTrading
  else if byte = 0x35 then .tradeReportingOnExchange
  else if byte = 0x36 then .tradeReportingOffExchange
  else if byte = 0x37 then .tradeReportingSystematicInternaliser
  else if byte = 0x49 then .scheduledIntradayAuctionequalUncrossing
  else if byte = 0x4B then .scheduledClosingAuctionequalUncrossing
  else if byte = 0x4F then .scheduledOpeningAuctionequalUncrossing
  else .unscheduledAuctionequalUncrossing

def ofByte (byte : UInt8) : MmtTradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MmtTradingMode) : ofByte value.toByte = value := by
  cases value with
  | undefinedAuctionequalUncrossing => decide
  | continuousTrading => decide
  | atMarketCloseTrading => decide
  | outofMainSessionTrading => decide
  | tradeReportingOnExchange => decide
  | tradeReportingOffExchange => decide
  | tradeReportingSystematicInternaliser => decide
  | scheduledIntradayAuctionequalUncrossing => decide
  | scheduledClosingAuctionequalUncrossing => decide
  | scheduledOpeningAuctionequalUncrossing => decide
  | unscheduledAuctionequalUncrossing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MmtTradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MmtTradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MmtTradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MmtTradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MmtTradingMode

/-- Mmt Off Book Automated Indicator: one byte code -/
def MmtOffBookAutomatedIndicator.codes : List UInt8 :=
  [0x4D, 0x51, 0x2D]

inductive MmtOffBookAutomatedIndicator where
  | offBookNonAutomated -- Off Book Non Automated
  | offBookAutomated -- Off Book Automated
  | unspecifiedordoesnotapply -- Unspecifiedordoesnotapply
  | unlisted (byte : { byte : UInt8 // byte ∉ MmtOffBookAutomatedIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MmtOffBookAutomatedIndicator

def toByte : MmtOffBookAutomatedIndicator → UInt8
  | .offBookNonAutomated => 0x4D
  | .offBookAutomated => 0x51
  | .unspecifiedordoesnotapply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MmtOffBookAutomatedIndicator :=
  if byte = 0x4D then .offBookNonAutomated
  else if byte = 0x51 then .offBookAutomated
  else .unspecifiedordoesnotapply

def ofByte (byte : UInt8) : MmtOffBookAutomatedIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MmtOffBookAutomatedIndicator) : ofByte value.toByte = value := by
  cases value with
  | offBookNonAutomated => decide
  | offBookAutomated => decide
  | unspecifiedordoesnotapply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MmtOffBookAutomatedIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MmtOffBookAutomatedIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MmtOffBookAutomatedIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MmtOffBookAutomatedIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MmtOffBookAutomatedIndicator

/-- Block Trade Code: one byte code -/
def BlockTradeCode.codes : List UInt8 :=
  [0x42, 0x4E, 0x2D]

inductive BlockTradeCode where
  | blockTrade -- Block Trade
  | regulartradeorNegotiateddeal -- Regulartradeor Negotiateddeal
  | undefined -- Undefined
  | unlisted (byte : { byte : UInt8 // byte ∉ BlockTradeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BlockTradeCode

def toByte : BlockTradeCode → UInt8
  | .blockTrade => 0x42
  | .regulartradeorNegotiateddeal => 0x4E
  | .undefined => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BlockTradeCode :=
  if byte = 0x42 then .blockTrade
  else if byte = 0x4E then .regulartradeorNegotiateddeal
  else .undefined

def ofByte (byte : UInt8) : BlockTradeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BlockTradeCode) : ofByte value.toByte = value := by
  cases value with
  | blockTrade => decide
  | regulartradeorNegotiateddeal => decide
  | undefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BlockTradeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BlockTradeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BlockTradeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BlockTradeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BlockTradeCode

/-- Type Of Market Admission: one byte code -/
def TypeOfMarketAdmission.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x53, 0x36, 0x37, 0x39]

inductive TypeOfMarketAdmission where
  | instrumentstradedontheprimarymarket -- Instrumentstradedontheprimarymarket
  | instrumentstradedonthesecondarymarket -- Instrumentstradedonthesecondarymarket
  | instrumentstradedontheNewMarket -- Instrumentstradedonthe New Market
  | nonregulatedmarketinstrumentstradedonthefreemarket -- Nonregulatedmarketinstrumentstradedonthefreemarket
  | nonregulatedmarketAlternext -- Nonregulatedmarket Alternext
  | nonlisted -- Nonlisted
  | regulatedMarketNonequities -- Regulated Market Nonequities
  | regulatedMarketEquitiesSegmentA -- Regulated Market Equities Segment A
  | regulatedMarketEquitiesSegmentB -- Regulated Market Equities Segment B
  | regulatedMarketEquitiesSegmentC -- Regulated Market Equities Segment C
  | regulatedMarketAllsecuritiesSpecialSegment -- Regulated Market Allsecurities Special Segment
  | regulatedMarketEquitiesOtherinstruments -- Regulated Market Equities Otherinstruments
  | opcvmsicomInonlistedFrenchInvestmentFunds -- Opcvmsicom Inonlisted French Investment Funds
  | offMarket -- Off Market
  | goldCurrenciesandIndices -- Gold Currenciesand Indices
  | foreign -- Foreign
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfMarketAdmission.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfMarketAdmission

def toByte : TypeOfMarketAdmission → UInt8
  | .instrumentstradedontheprimarymarket => 0x41
  | .instrumentstradedonthesecondarymarket => 0x42
  | .instrumentstradedontheNewMarket => 0x43
  | .nonregulatedmarketinstrumentstradedonthefreemarket => 0x44
  | .nonregulatedmarketAlternext => 0x45
  | .nonlisted => 0x46
  | .regulatedMarketNonequities => 0x47
  | .regulatedMarketEquitiesSegmentA => 0x48
  | .regulatedMarketEquitiesSegmentB => 0x49
  | .regulatedMarketEquitiesSegmentC => 0x4A
  | .regulatedMarketAllsecuritiesSpecialSegment => 0x4B
  | .regulatedMarketEquitiesOtherinstruments => 0x4C
  | .opcvmsicomInonlistedFrenchInvestmentFunds => 0x53
  | .offMarket => 0x36
  | .goldCurrenciesandIndices => 0x37
  | .foreign => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfMarketAdmission :=
  if byte = 0x41 then .instrumentstradedontheprimarymarket
  else if byte = 0x42 then .instrumentstradedonthesecondarymarket
  else if byte = 0x43 then .instrumentstradedontheNewMarket
  else if byte = 0x44 then .nonregulatedmarketinstrumentstradedonthefreemarket
  else if byte = 0x45 then .nonregulatedmarketAlternext
  else if byte = 0x46 then .nonlisted
  else if byte = 0x47 then .regulatedMarketNonequities
  else if byte = 0x48 then .regulatedMarketEquitiesSegmentA
  else if byte = 0x49 then .regulatedMarketEquitiesSegmentB
  else if byte = 0x4A then .regulatedMarketEquitiesSegmentC
  else if byte = 0x4B then .regulatedMarketAllsecuritiesSpecialSegment
  else if byte = 0x4C then .regulatedMarketEquitiesOtherinstruments
  else if byte = 0x53 then .opcvmsicomInonlistedFrenchInvestmentFunds
  else if byte = 0x36 then .offMarket
  else if byte = 0x37 then .goldCurrenciesandIndices
  else .foreign

def ofByte (byte : UInt8) : TypeOfMarketAdmission :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfMarketAdmission) : ofByte value.toByte = value := by
  cases value with
  | instrumentstradedontheprimarymarket => decide
  | instrumentstradedonthesecondarymarket => decide
  | instrumentstradedontheNewMarket => decide
  | nonregulatedmarketinstrumentstradedonthefreemarket => decide
  | nonregulatedmarketAlternext => decide
  | nonlisted => decide
  | regulatedMarketNonequities => decide
  | regulatedMarketEquitiesSegmentA => decide
  | regulatedMarketEquitiesSegmentB => decide
  | regulatedMarketEquitiesSegmentC => decide
  | regulatedMarketAllsecuritiesSpecialSegment => decide
  | regulatedMarketEquitiesOtherinstruments => decide
  | opcvmsicomInonlistedFrenchInvestmentFunds => decide
  | offMarket => decide
  | goldCurrenciesandIndices => decide
  | foreign => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfMarketAdmission) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfMarketAdmission × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfMarketAdmission) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfMarketAdmission) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfMarketAdmission

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x50, 0x52, 0x53, 0x59, 0x5A, 0x4E, 0x4F, 0x4C]

inductive ExchangeCode where
  | amsterdamEquityDerivatives -- Amsterdam Equity Derivatives
  | brusselsEquityDerivatives -- Brussels Equity Derivatives
  | parisEquityUnderlyings -- Paris Equity Underlyings
  | brusselsCashUnderlyings -- Brussels Cash Underlyings
  | brusselsIndexDerivatives -- Brussels Index Derivatives
  | amsterdamCashUnderlyings -- Amsterdam Cash Underlyings
  | lisbonCashUnderlyings -- Lisbon Cash Underlyings
  | parisIndexDerivatives -- Paris Index Derivatives
  | amsterdamIndexDerivatives -- Amsterdam Index Derivatives
  | lisbonIndexDerivatives -- Lisbon Index Derivatives
  | parisEquityDerivatives -- Paris Equity Derivatives
  | amsterdamCommoditiesDerivatives -- Amsterdam Commodities Derivatives
  | lisbonEquityDerivatives -- Lisbon Equity Derivatives
  | parisCommoditiesDerivatives -- Paris Commodities Derivatives
  | amsterdamCurrencyDerivatives -- Amsterdam Currency Derivatives
  | osloIndexDerivatives -- Oslo Index Derivatives
  | osloEquityDerivatives -- Oslo Equity Derivatives
  | osloCashUnderlying -- Oslo Cash Underlying
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .amsterdamEquityDerivatives => 0x41
  | .brusselsEquityDerivatives => 0x42
  | .parisEquityUnderlyings => 0x43
  | .brusselsCashUnderlyings => 0x44
  | .brusselsIndexDerivatives => 0x46
  | .amsterdamCashUnderlyings => 0x47
  | .lisbonCashUnderlyings => 0x48
  | .parisIndexDerivatives => 0x4A
  | .amsterdamIndexDerivatives => 0x4B
  | .lisbonIndexDerivatives => 0x4D
  | .parisEquityDerivatives => 0x50
  | .amsterdamCommoditiesDerivatives => 0x52
  | .lisbonEquityDerivatives => 0x53
  | .parisCommoditiesDerivatives => 0x59
  | .amsterdamCurrencyDerivatives => 0x5A
  | .osloIndexDerivatives => 0x4E
  | .osloEquityDerivatives => 0x4F
  | .osloCashUnderlying => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .amsterdamEquityDerivatives
  else if byte = 0x42 then .brusselsEquityDerivatives
  else if byte = 0x43 then .parisEquityUnderlyings
  else if byte = 0x44 then .brusselsCashUnderlyings
  else if byte = 0x46 then .brusselsIndexDerivatives
  else if byte = 0x47 then .amsterdamCashUnderlyings
  else if byte = 0x48 then .lisbonCashUnderlyings
  else if byte = 0x4A then .parisIndexDerivatives
  else if byte = 0x4B then .amsterdamIndexDerivatives
  else if byte = 0x4D then .lisbonIndexDerivatives
  else if byte = 0x50 then .parisEquityDerivatives
  else if byte = 0x52 then .amsterdamCommoditiesDerivatives
  else if byte = 0x53 then .lisbonEquityDerivatives
  else if byte = 0x59 then .parisCommoditiesDerivatives
  else if byte = 0x5A then .amsterdamCurrencyDerivatives
  else if byte = 0x4E then .osloIndexDerivatives
  else if byte = 0x4F then .osloEquityDerivatives
  else .osloCashUnderlying

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | amsterdamEquityDerivatives => decide
  | brusselsEquityDerivatives => decide
  | parisEquityUnderlyings => decide
  | brusselsCashUnderlyings => decide
  | brusselsIndexDerivatives => decide
  | amsterdamCashUnderlyings => decide
  | lisbonCashUnderlyings => decide
  | parisIndexDerivatives => decide
  | amsterdamIndexDerivatives => decide
  | lisbonIndexDerivatives => decide
  | parisEquityDerivatives => decide
  | amsterdamCommoditiesDerivatives => decide
  | lisbonEquityDerivatives => decide
  | parisCommoditiesDerivatives => decide
  | amsterdamCurrencyDerivatives => decide
  | osloIndexDerivatives => decide
  | osloEquityDerivatives => decide
  | osloCashUnderlying => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Strategy Code: one byte code -/
def StrategyCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6D, 0x6E, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A]

inductive StrategyCode where
  | jellyRoll -- Jelly Roll
  | butterfly -- Butterfly
  | callorPutCabinet -- Callor Put Cabinet
  | spread -- Spread
  | calendarSpread -- Calendar Spread
  | diagonalCalendarSpread -- Diagonal Calendar Spread
  | guts -- Guts
  | twobyOneRatioSpread -- Twoby One Ratio Spread
  | ironButterfly -- Iron Butterfly
  | combo -- Combo
  | strangle -- Strangle
  | ladder -- Ladder
  | strip -- Strip
  | straddleCalendarSpread -- Straddle Calendar Spread
  | pack -- Pack
  | diagonalStraddleCalendarSpread -- Diagonal Straddle Calendar Spread
  | simpleInterCommoditySpread -- Simple Inter Commodity Spread
  | conversionReversal -- Conversion Reversal
  | straddle -- Straddle
  | volatilityTrade -- Volatility Trade
  | condor -- Condor
  | box -- Box
  | bundle -- Bundle
  | reducedTickSpread -- Reduced Tick Spread
  | ladderversusUnderlying -- Ladderversus Underlying
  | butterflyversusUnderlying -- Butterflyversus Underlying
  | callSpreadversusPutversusUnderlying -- Call Spreadversus Putversus Underlying
  | callorPutSpreadversusUnderlying -- Callor Put Spreadversus Underlying
  | callorPutCalendarSpreadversusUnderlying -- Callor Put Calendar Spreadversus Underlying
  | callPutDiagonalCalendarSpreadversusUnderlying -- Call Put Diagonal Calendar Spreadversus Underlying
  | gutsversusUnderlying -- Gutsversus Underlying
  | twobyOneCallorPutRatioSpreadversusUnderlying -- Twoby One Callor Put Ratio Spreadversus Underlying
  | ironButterflyversusUnderlying -- Iron Butterflyversus Underlying
  | comboversusUnderlying -- Comboversus Underlying
  | strangleversusUnderlying -- Strangleversus Underlying
  | exchangeforPhysical -- Exchangefor Physical
  | straddleCalendarSpreadversusUnderlying -- Straddle Calendar Spreadversus Underlying
  | putSpreadversusCallversusUnderlying -- Put Spreadversus Callversus Underlying
  | diagonalStraddleCalendarSpreadversusUnderlying -- Diagonal Straddle Calendar Spreadversus Underlying
  | synthetic -- Synthetic
  | straddleversusUnderlying -- Straddleversus Underlying
  | condorversusUnderlying -- Condorversus Underlying
  | buyWrite -- Buy Write
  | ironCondorversusUnderlying -- Iron Condorversus Underlying
  | ironCondor -- Iron Condor
  | callSpreadversusSellaPut -- Call Spreadversus Sella Put
  | putSpreadversusSellaCall -- Put Spreadversus Sella Call
  | putStraddleversusSellaCalloraPut -- Put Straddleversus Sella Callora Put
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyCode

def toByte : StrategyCode → UInt8
  | .jellyRoll => 0x41
  | .butterfly => 0x42
  | .callorPutCabinet => 0x43
  | .spread => 0x44
  | .calendarSpread => 0x45
  | .diagonalCalendarSpread => 0x46
  | .guts => 0x47
  | .twobyOneRatioSpread => 0x48
  | .ironButterfly => 0x49
  | .combo => 0x4A
  | .strangle => 0x4B
  | .ladder => 0x4C
  | .strip => 0x4D
  | .straddleCalendarSpread => 0x4E
  | .pack => 0x4F
  | .diagonalStraddleCalendarSpread => 0x50
  | .simpleInterCommoditySpread => 0x51
  | .conversionReversal => 0x52
  | .straddle => 0x53
  | .volatilityTrade => 0x56
  | .condor => 0x57
  | .box => 0x58
  | .bundle => 0x59
  | .reducedTickSpread => 0x5A
  | .ladderversusUnderlying => 0x61
  | .butterflyversusUnderlying => 0x62
  | .callSpreadversusPutversusUnderlying => 0x63
  | .callorPutSpreadversusUnderlying => 0x64
  | .callorPutCalendarSpreadversusUnderlying => 0x65
  | .callPutDiagonalCalendarSpreadversusUnderlying => 0x66
  | .gutsversusUnderlying => 0x67
  | .twobyOneCallorPutRatioSpreadversusUnderlying => 0x68
  | .ironButterflyversusUnderlying => 0x69
  | .comboversusUnderlying => 0x6A
  | .strangleversusUnderlying => 0x6B
  | .exchangeforPhysical => 0x6D
  | .straddleCalendarSpreadversusUnderlying => 0x6E
  | .putSpreadversusCallversusUnderlying => 0x70
  | .diagonalStraddleCalendarSpreadversusUnderlying => 0x71
  | .synthetic => 0x72
  | .straddleversusUnderlying => 0x73
  | .condorversusUnderlying => 0x74
  | .buyWrite => 0x75
  | .ironCondorversusUnderlying => 0x76
  | .ironCondor => 0x77
  | .callSpreadversusSellaPut => 0x78
  | .putSpreadversusSellaCall => 0x79
  | .putStraddleversusSellaCalloraPut => 0x7A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyCode :=
  if byte = 0x41 then .jellyRoll
  else if byte = 0x42 then .butterfly
  else if byte = 0x43 then .callorPutCabinet
  else if byte = 0x44 then .spread
  else if byte = 0x45 then .calendarSpread
  else if byte = 0x46 then .diagonalCalendarSpread
  else if byte = 0x47 then .guts
  else if byte = 0x48 then .twobyOneRatioSpread
  else if byte = 0x49 then .ironButterfly
  else if byte = 0x4A then .combo
  else if byte = 0x4B then .strangle
  else if byte = 0x4C then .ladder
  else if byte = 0x4D then .strip
  else if byte = 0x4E then .straddleCalendarSpread
  else if byte = 0x4F then .pack
  else if byte = 0x50 then .diagonalStraddleCalendarSpread
  else if byte = 0x51 then .simpleInterCommoditySpread
  else if byte = 0x52 then .conversionReversal
  else if byte = 0x53 then .straddle
  else if byte = 0x56 then .volatilityTrade
  else if byte = 0x57 then .condor
  else if byte = 0x58 then .box
  else if byte = 0x59 then .bundle
  else if byte = 0x5A then .reducedTickSpread
  else if byte = 0x61 then .ladderversusUnderlying
  else if byte = 0x62 then .butterflyversusUnderlying
  else if byte = 0x63 then .callSpreadversusPutversusUnderlying
  else if byte = 0x64 then .callorPutSpreadversusUnderlying
  else if byte = 0x65 then .callorPutCalendarSpreadversusUnderlying
  else if byte = 0x66 then .callPutDiagonalCalendarSpreadversusUnderlying
  else if byte = 0x67 then .gutsversusUnderlying
  else if byte = 0x68 then .twobyOneCallorPutRatioSpreadversusUnderlying
  else if byte = 0x69 then .ironButterflyversusUnderlying
  else if byte = 0x6A then .comboversusUnderlying
  else if byte = 0x6B then .strangleversusUnderlying
  else if byte = 0x6D then .exchangeforPhysical
  else if byte = 0x6E then .straddleCalendarSpreadversusUnderlying
  else if byte = 0x70 then .putSpreadversusCallversusUnderlying
  else if byte = 0x71 then .diagonalStraddleCalendarSpreadversusUnderlying
  else if byte = 0x72 then .synthetic
  else if byte = 0x73 then .straddleversusUnderlying
  else if byte = 0x74 then .condorversusUnderlying
  else if byte = 0x75 then .buyWrite
  else if byte = 0x76 then .ironCondorversusUnderlying
  else if byte = 0x77 then .ironCondor
  else if byte = 0x78 then .callSpreadversusSellaPut
  else if byte = 0x79 then .putSpreadversusSellaCall
  else .putStraddleversusSellaCalloraPut

def ofByte (byte : UInt8) : StrategyCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyCode) : ofByte value.toByte = value := by
  cases value with
  | jellyRoll => decide
  | butterfly => decide
  | callorPutCabinet => decide
  | spread => decide
  | calendarSpread => decide
  | diagonalCalendarSpread => decide
  | guts => decide
  | twobyOneRatioSpread => decide
  | ironButterfly => decide
  | combo => decide
  | strangle => decide
  | ladder => decide
  | strip => decide
  | straddleCalendarSpread => decide
  | pack => decide
  | diagonalStraddleCalendarSpread => decide
  | simpleInterCommoditySpread => decide
  | conversionReversal => decide
  | straddle => decide
  | volatilityTrade => decide
  | condor => decide
  | box => decide
  | bundle => decide
  | reducedTickSpread => decide
  | ladderversusUnderlying => decide
  | butterflyversusUnderlying => decide
  | callSpreadversusPutversusUnderlying => decide
  | callorPutSpreadversusUnderlying => decide
  | callorPutCalendarSpreadversusUnderlying => decide
  | callPutDiagonalCalendarSpreadversusUnderlying => decide
  | gutsversusUnderlying => decide
  | twobyOneCallorPutRatioSpreadversusUnderlying => decide
  | ironButterflyversusUnderlying => decide
  | comboversusUnderlying => decide
  | strangleversusUnderlying => decide
  | exchangeforPhysical => decide
  | straddleCalendarSpreadversusUnderlying => decide
  | putSpreadversusCallversusUnderlying => decide
  | diagonalStraddleCalendarSpreadversusUnderlying => decide
  | synthetic => decide
  | straddleversusUnderlying => decide
  | condorversusUnderlying => decide
  | buyWrite => decide
  | ironCondorversusUnderlying => decide
  | ironCondor => decide
  | callSpreadversusSellaPut => decide
  | putSpreadversusSellaCall => decide
  | putStraddleversusSellaCalloraPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyCode

/-- Leg Buy Sell: one byte code -/
def LegBuySell.codes : List UInt8 :=
  [0x42, 0x53]

inductive LegBuySell where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegBuySell.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegBuySell

def toByte : LegBuySell → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegBuySell :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : LegBuySell :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegBuySell) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegBuySell) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegBuySell × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegBuySell) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegBuySell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegBuySell

/-- Contract Type: one byte code -/
def ContractType.codes : List UInt8 :=
  [0x46, 0x4F, 0x55]

inductive ContractType where
  | future -- Future
  | option -- Option
  | underlying -- Underlying
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractType

def toByte : ContractType → UInt8
  | .future => 0x46
  | .option => 0x4F
  | .underlying => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractType :=
  if byte = 0x46 then .future
  else if byte = 0x4F then .option
  else .underlying

def ofByte (byte : UInt8) : ContractType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractType) : ofByte value.toByte = value := by
  cases value with
  | future => decide
  | option => decide
  | underlying => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContractType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractType

/-- Underlying Type: one byte code -/
def UnderlyingType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x5A]

inductive UnderlyingType where
  | basketwithCommodity -- Basketwith Commodity
  | basket -- Basket
  | commodity -- Commodity
  | depositaryReceipt -- Depositary Receipt
  | future -- Future
  | currencyLeveragedIndex -- Currency Leveraged Index
  | other -- Other
  | index -- Index
  | bonds -- Bonds
  | stockDividend -- Stock Dividend
  | leveragedIndex -- Leveraged Index
  | interestRate -- Interest Rate
  | otherDerivative -- Other Derivative
  | commodityIndex -- Commodity Index
  | commodityLeveragedIndex -- Commodity Leveraged Index
  | right -- Right
  | stock -- Stock
  | credit -- Credit
  | fund -- Fund
  | currency -- Currency
  | stockWarrant -- Stock Warrant
  | exchangeRate -- Exchange Rate
  | securityLeveragedIndex -- Security Leveraged Index
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingType

def toByte : UnderlyingType → UInt8
  | .basketwithCommodity => 0x41
  | .basket => 0x42
  | .commodity => 0x43
  | .depositaryReceipt => 0x44
  | .future => 0x46
  | .currencyLeveragedIndex => 0x47
  | .other => 0x48
  | .index => 0x49
  | .bonds => 0x4A
  | .stockDividend => 0x4B
  | .leveragedIndex => 0x4C
  | .interestRate => 0x4E
  | .otherDerivative => 0x4F
  | .commodityIndex => 0x50
  | .commodityLeveragedIndex => 0x51
  | .right => 0x52
  | .stock => 0x53
  | .credit => 0x54
  | .fund => 0x55
  | .currency => 0x56
  | .stockWarrant => 0x57
  | .exchangeRate => 0x58
  | .securityLeveragedIndex => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingType :=
  if byte = 0x41 then .basketwithCommodity
  else if byte = 0x42 then .basket
  else if byte = 0x43 then .commodity
  else if byte = 0x44 then .depositaryReceipt
  else if byte = 0x46 then .future
  else if byte = 0x47 then .currencyLeveragedIndex
  else if byte = 0x48 then .other
  else if byte = 0x49 then .index
  else if byte = 0x4A then .bonds
  else if byte = 0x4B then .stockDividend
  else if byte = 0x4C then .leveragedIndex
  else if byte = 0x4E then .interestRate
  else if byte = 0x4F then .otherDerivative
  else if byte = 0x50 then .commodityIndex
  else if byte = 0x51 then .commodityLeveragedIndex
  else if byte = 0x52 then .right
  else if byte = 0x53 then .stock
  else if byte = 0x54 then .credit
  else if byte = 0x55 then .fund
  else if byte = 0x56 then .currency
  else if byte = 0x57 then .stockWarrant
  else if byte = 0x58 then .exchangeRate
  else .securityLeveragedIndex

def ofByte (byte : UInt8) : UnderlyingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingType) : ofByte value.toByte = value := by
  cases value with
  | basketwithCommodity => decide
  | basket => decide
  | commodity => decide
  | depositaryReceipt => decide
  | future => decide
  | currencyLeveragedIndex => decide
  | other => decide
  | index => decide
  | bonds => decide
  | stockDividend => decide
  | leveragedIndex => decide
  | interestRate => decide
  | otherDerivative => decide
  | commodityIndex => decide
  | commodityLeveragedIndex => decide
  | right => decide
  | stock => decide
  | credit => decide
  | fund => decide
  | currency => decide
  | stockWarrant => decide
  | exchangeRate => decide
  | securityLeveragedIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UnderlyingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingType

/-- Efficient Mmt Trading Mode: one byte code -/
def EfficientMmtTradingMode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x49, 0x4B, 0x4F, 0x55]

inductive EfficientMmtTradingMode where
  | undefinedAuctionequalUncrossing -- Undefined Auctionequal Uncrossing
  | continuousTrading -- Continuous Trading
  | atMarketCloseTrading -- At Market Close Trading
  | outofMainSessionTrading -- Outof Main Session Trading
  | tradeReportingOnExchange -- Trade Reporting On Exchange
  | tradeReportingOffExchange -- Trade Reporting Off Exchange
  | tradeReportingSystematicInternaliser -- Trade Reporting Systematic Internaliser
  | scheduledIntradayAuctionequalUncrossing -- Scheduled Intraday Auctionequal Uncrossing
  | scheduledClosingAuctionequalUncrossing -- Scheduled Closing Auctionequal Uncrossing
  | scheduledOpeningAuctionequalUncrossing -- Scheduled Opening Auctionequal Uncrossing
  | unscheduledAuctionequalUncrossing -- Unscheduled Auctionequal Uncrossing
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtTradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtTradingMode

def toByte : EfficientMmtTradingMode → UInt8
  | .undefinedAuctionequalUncrossing => 0x31
  | .continuousTrading => 0x32
  | .atMarketCloseTrading => 0x33
  | .outofMainSessionTrading => 0x34
  | .tradeReportingOnExchange => 0x35
  | .tradeReportingOffExchange => 0x36
  | .tradeReportingSystematicInternaliser => 0x37
  | .scheduledIntradayAuctionequalUncrossing => 0x49
  | .scheduledClosingAuctionequalUncrossing => 0x4B
  | .scheduledOpeningAuctionequalUncrossing => 0x4F
  | .unscheduledAuctionequalUncrossing => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtTradingMode :=
  if byte = 0x31 then .undefinedAuctionequalUncrossing
  else if byte = 0x32 then .continuousTrading
  else if byte = 0x33 then .atMarketCloseTrading
  else if byte = 0x34 then .outofMainSessionTrading
  else if byte = 0x35 then .tradeReportingOnExchange
  else if byte = 0x36 then .tradeReportingOffExchange
  else if byte = 0x37 then .tradeReportingSystematicInternaliser
  else if byte = 0x49 then .scheduledIntradayAuctionequalUncrossing
  else if byte = 0x4B then .scheduledClosingAuctionequalUncrossing
  else if byte = 0x4F then .scheduledOpeningAuctionequalUncrossing
  else .unscheduledAuctionequalUncrossing

def ofByte (byte : UInt8) : EfficientMmtTradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtTradingMode) : ofByte value.toByte = value := by
  cases value with
  | undefinedAuctionequalUncrossing => decide
  | continuousTrading => decide
  | atMarketCloseTrading => decide
  | outofMainSessionTrading => decide
  | tradeReportingOnExchange => decide
  | tradeReportingOffExchange => decide
  | tradeReportingSystematicInternaliser => decide
  | scheduledIntradayAuctionequalUncrossing => decide
  | scheduledClosingAuctionequalUncrossing => decide
  | scheduledOpeningAuctionequalUncrossing => decide
  | unscheduledAuctionequalUncrossing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtTradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtTradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtTradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtTradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtTradingMode

/-- Efficient Mmt Transaction Category: one byte code -/
def EfficientMmtTransactionCategory.codes : List UInt8 :=
  [0x44, 0x52, 0x59, 0x5A, 0x2D]

inductive EfficientMmtTransactionCategory where
  | darkTrade -- Dark Trade
  | rpri -- Rpri
  | xfph -- Xfph
  | tpac -- Tpac
  | noneapply -- Noneapply
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtTransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtTransactionCategory

def toByte : EfficientMmtTransactionCategory → UInt8
  | .darkTrade => 0x44
  | .rpri => 0x52
  | .xfph => 0x59
  | .tpac => 0x5A
  | .noneapply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtTransactionCategory :=
  if byte = 0x44 then .darkTrade
  else if byte = 0x52 then .rpri
  else if byte = 0x59 then .xfph
  else if byte = 0x5A then .tpac
  else .noneapply

def ofByte (byte : UInt8) : EfficientMmtTransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtTransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | darkTrade => decide
  | rpri => decide
  | xfph => decide
  | tpac => decide
  | noneapply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtTransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtTransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtTransactionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtTransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtTransactionCategory

/-- Efficient Mmt Negotiation Indicator: one byte code -/
def EfficientMmtNegotiationIndicator.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x4E, 0x2D]

inductive EfficientMmtNegotiationIndicator where
  | nliq -- Nliq
  | oilq -- Oilq
  | pric -- Pric
  | ilqd -- Ilqd
  | size -- Size
  | ilqdSize -- Ilqd Size
  | negotiatedTrade -- Negotiated Trade
  | noNegotiatedTrade -- No Negotiated Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtNegotiationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtNegotiationIndicator

def toByte : EfficientMmtNegotiationIndicator → UInt8
  | .nliq => 0x31
  | .oilq => 0x32
  | .pric => 0x33
  | .ilqd => 0x34
  | .size => 0x35
  | .ilqdSize => 0x36
  | .negotiatedTrade => 0x4E
  | .noNegotiatedTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtNegotiationIndicator :=
  if byte = 0x31 then .nliq
  else if byte = 0x32 then .oilq
  else if byte = 0x33 then .pric
  else if byte = 0x34 then .ilqd
  else if byte = 0x35 then .size
  else if byte = 0x36 then .ilqdSize
  else if byte = 0x4E then .negotiatedTrade
  else .noNegotiatedTrade

def ofByte (byte : UInt8) : EfficientMmtNegotiationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtNegotiationIndicator) : ofByte value.toByte = value := by
  cases value with
  | nliq => decide
  | oilq => decide
  | pric => decide
  | ilqd => decide
  | size => decide
  | ilqdSize => decide
  | negotiatedTrade => decide
  | noNegotiatedTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtNegotiationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtNegotiationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtNegotiationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtNegotiationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtNegotiationIndicator

/-- Efficient Mmt Agency Cross Trade Indicator: one byte code -/
def EfficientMmtAgencyCrossTradeIndicator.codes : List UInt8 :=
  [0x58, 0x2D]

inductive EfficientMmtAgencyCrossTradeIndicator where
  | actx -- Actx
  | noAgencyCrossTrade -- No Agency Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtAgencyCrossTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtAgencyCrossTradeIndicator

def toByte : EfficientMmtAgencyCrossTradeIndicator → UInt8
  | .actx => 0x58
  | .noAgencyCrossTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtAgencyCrossTradeIndicator :=
  if byte = 0x58 then .actx
  else .noAgencyCrossTrade

def ofByte (byte : UInt8) : EfficientMmtAgencyCrossTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtAgencyCrossTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | actx => decide
  | noAgencyCrossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtAgencyCrossTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtAgencyCrossTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtAgencyCrossTradeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtAgencyCrossTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtAgencyCrossTradeIndicator

/-- Efficient Mmt Modification Indicator: one byte code -/
def EfficientMmtModificationIndicator.codes : List UInt8 :=
  [0x41, 0x43, 0x2D]

inductive EfficientMmtModificationIndicator where
  | amnd -- Amnd
  | canc -- Canc
  | newTrade -- New Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtModificationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtModificationIndicator

def toByte : EfficientMmtModificationIndicator → UInt8
  | .amnd => 0x41
  | .canc => 0x43
  | .newTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtModificationIndicator :=
  if byte = 0x41 then .amnd
  else if byte = 0x43 then .canc
  else .newTrade

def ofByte (byte : UInt8) : EfficientMmtModificationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtModificationIndicator) : ofByte value.toByte = value := by
  cases value with
  | amnd => decide
  | canc => decide
  | newTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtModificationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtModificationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtModificationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtModificationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtModificationIndicator

/-- Efficient Mmt Benchmark Indicator: one byte code -/
def EfficientMmtBenchmarkIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x2D]

inductive EfficientMmtBenchmarkIndicator where
  | benc -- Benc
  | rfpt -- Rfpt
  | noBenchmarkorReferencePriceTrade -- No Benchmarkor Reference Price Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtBenchmarkIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtBenchmarkIndicator

def toByte : EfficientMmtBenchmarkIndicator → UInt8
  | .benc => 0x42
  | .rfpt => 0x53
  | .noBenchmarkorReferencePriceTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtBenchmarkIndicator :=
  if byte = 0x42 then .benc
  else if byte = 0x53 then .rfpt
  else .noBenchmarkorReferencePriceTrade

def ofByte (byte : UInt8) : EfficientMmtBenchmarkIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtBenchmarkIndicator) : ofByte value.toByte = value := by
  cases value with
  | benc => decide
  | rfpt => decide
  | noBenchmarkorReferencePriceTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtBenchmarkIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtBenchmarkIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtBenchmarkIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtBenchmarkIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtBenchmarkIndicator

/-- Efficient Mmt Special Dividend Indicator: one byte code -/
def EfficientMmtSpecialDividendIndicator.codes : List UInt8 :=
  [0x45, 0x2D]

inductive EfficientMmtSpecialDividendIndicator where
  | sdiv -- Sdiv
  | noSpecialDividendTrade -- No Special Dividend Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtSpecialDividendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtSpecialDividendIndicator

def toByte : EfficientMmtSpecialDividendIndicator → UInt8
  | .sdiv => 0x45
  | .noSpecialDividendTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtSpecialDividendIndicator :=
  if byte = 0x45 then .sdiv
  else .noSpecialDividendTrade

def ofByte (byte : UInt8) : EfficientMmtSpecialDividendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtSpecialDividendIndicator) : ofByte value.toByte = value := by
  cases value with
  | sdiv => decide
  | noSpecialDividendTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtSpecialDividendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtSpecialDividendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtSpecialDividendIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtSpecialDividendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtSpecialDividendIndicator

/-- Efficient Mmt Off Book Automated Indicator: one byte code -/
def EfficientMmtOffBookAutomatedIndicator.codes : List UInt8 :=
  [0x4D, 0x51, 0x2D]

inductive EfficientMmtOffBookAutomatedIndicator where
  | offBookNonAutomated -- Off Book Non Automated
  | offBookAutomated -- Off Book Automated
  | unspecifiedordoesnotapply -- Unspecifiedordoesnotapply
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtOffBookAutomatedIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtOffBookAutomatedIndicator

def toByte : EfficientMmtOffBookAutomatedIndicator → UInt8
  | .offBookNonAutomated => 0x4D
  | .offBookAutomated => 0x51
  | .unspecifiedordoesnotapply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtOffBookAutomatedIndicator :=
  if byte = 0x4D then .offBookNonAutomated
  else if byte = 0x51 then .offBookAutomated
  else .unspecifiedordoesnotapply

def ofByte (byte : UInt8) : EfficientMmtOffBookAutomatedIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtOffBookAutomatedIndicator) : ofByte value.toByte = value := by
  cases value with
  | offBookNonAutomated => decide
  | offBookAutomated => decide
  | unspecifiedordoesnotapply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtOffBookAutomatedIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtOffBookAutomatedIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtOffBookAutomatedIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtOffBookAutomatedIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtOffBookAutomatedIndicator

/-- Efficient Mmt Contributionto Price: one byte code -/
def EfficientMmtContributiontoPrice.codes : List UInt8 :=
  [0x4A, 0x4E, 0x50, 0x54]

inductive EfficientMmtContributiontoPrice where
  | tncp -- Tncp
  | pndg -- Pndg
  | plainVanillaTrade -- Plain Vanilla Trade
  | npft -- Npft
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtContributiontoPrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtContributiontoPrice

def toByte : EfficientMmtContributiontoPrice → UInt8
  | .tncp => 0x4A
  | .pndg => 0x4E
  | .plainVanillaTrade => 0x50
  | .npft => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtContributiontoPrice :=
  if byte = 0x4A then .tncp
  else if byte = 0x4E then .pndg
  else if byte = 0x50 then .plainVanillaTrade
  else .npft

def ofByte (byte : UInt8) : EfficientMmtContributiontoPrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtContributiontoPrice) : ofByte value.toByte = value := by
  cases value with
  | tncp => decide
  | pndg => decide
  | plainVanillaTrade => decide
  | npft => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtContributiontoPrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtContributiontoPrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtContributiontoPrice) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtContributiontoPrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtContributiontoPrice

/-- Efficient Mmt Algorithmic Indicator: one byte code -/
def EfficientMmtAlgorithmicIndicator.codes : List UInt8 :=
  [0x48, 0x2D]

inductive EfficientMmtAlgorithmicIndicator where
  | algo -- Algo
  | noAlgorithmicTrade -- No Algorithmic Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtAlgorithmicIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtAlgorithmicIndicator

def toByte : EfficientMmtAlgorithmicIndicator → UInt8
  | .algo => 0x48
  | .noAlgorithmicTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtAlgorithmicIndicator :=
  if byte = 0x48 then .algo
  else .noAlgorithmicTrade

def ofByte (byte : UInt8) : EfficientMmtAlgorithmicIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtAlgorithmicIndicator) : ofByte value.toByte = value := by
  cases value with
  | algo => decide
  | noAlgorithmicTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtAlgorithmicIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtAlgorithmicIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtAlgorithmicIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtAlgorithmicIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtAlgorithmicIndicator

/-- Efficient Mmt Publication Mode: one byte code -/
def EfficientMmtPublicationMode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x2D]

inductive EfficientMmtPublicationMode where
  | nonImmediatePublication -- Non Immediate Publication
  | lrgs -- Lrgs
  | ilqd -- Ilqd
  | size -- Size
  | ilqdSize -- Ilqd Size
  | ilqdLrgs -- Ilqd Lrgs
  | immediatePublication -- Immediate Publication
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtPublicationMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtPublicationMode

def toByte : EfficientMmtPublicationMode → UInt8
  | .nonImmediatePublication => 0x31
  | .lrgs => 0x32
  | .ilqd => 0x33
  | .size => 0x34
  | .ilqdSize => 0x35
  | .ilqdLrgs => 0x36
  | .immediatePublication => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtPublicationMode :=
  if byte = 0x31 then .nonImmediatePublication
  else if byte = 0x32 then .lrgs
  else if byte = 0x33 then .ilqd
  else if byte = 0x34 then .size
  else if byte = 0x35 then .ilqdSize
  else if byte = 0x36 then .ilqdLrgs
  else .immediatePublication

def ofByte (byte : UInt8) : EfficientMmtPublicationMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtPublicationMode) : ofByte value.toByte = value := by
  cases value with
  | nonImmediatePublication => decide
  | lrgs => decide
  | ilqd => decide
  | size => decide
  | ilqdSize => decide
  | ilqdLrgs => decide
  | immediatePublication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtPublicationMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtPublicationMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtPublicationMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtPublicationMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtPublicationMode

/-- Efficient Mmt Post Trade Deferral: one byte code -/
def EfficientMmtPostTradeDeferral.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x56, 0x57, 0x2D]

inductive EfficientMmtPostTradeDeferral where
  | lmtf -- Lmtf
  | datf -- Datf
  | volo -- Volo
  | fwaf -- Fwaf
  | idaf -- Idaf
  | volw -- Volw
  | fulf -- Fulf
  | fula -- Fula
  | fulv -- Fulv
  | fulj -- Fulj
  | coaf -- Coaf
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtPostTradeDeferral.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtPostTradeDeferral

def toByte : EfficientMmtPostTradeDeferral → UInt8
  | .lmtf => 0x31
  | .datf => 0x32
  | .volo => 0x33
  | .fwaf => 0x34
  | .idaf => 0x35
  | .volw => 0x36
  | .fulf => 0x37
  | .fula => 0x38
  | .fulv => 0x39
  | .fulj => 0x56
  | .coaf => 0x57
  | .notApplicable => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtPostTradeDeferral :=
  if byte = 0x31 then .lmtf
  else if byte = 0x32 then .datf
  else if byte = 0x33 then .volo
  else if byte = 0x34 then .fwaf
  else if byte = 0x35 then .idaf
  else if byte = 0x36 then .volw
  else if byte = 0x37 then .fulf
  else if byte = 0x38 then .fula
  else if byte = 0x39 then .fulv
  else if byte = 0x56 then .fulj
  else if byte = 0x57 then .coaf
  else .notApplicable

def ofByte (byte : UInt8) : EfficientMmtPostTradeDeferral :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtPostTradeDeferral) : ofByte value.toByte = value := by
  cases value with
  | lmtf => decide
  | datf => decide
  | volo => decide
  | fwaf => decide
  | idaf => decide
  | volw => decide
  | fulf => decide
  | fula => decide
  | fulv => decide
  | fulj => decide
  | coaf => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtPostTradeDeferral) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtPostTradeDeferral × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtPostTradeDeferral) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtPostTradeDeferral) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtPostTradeDeferral

/-- Efficient Mmt Duplicative Indicator: one byte code -/
def EfficientMmtDuplicativeIndicator.codes : List UInt8 :=
  [0x31, 0x2D]

inductive EfficientMmtDuplicativeIndicator where
  | dupl -- Dupl
  | uniqueTradeReport -- Unique Trade Report
  | unlisted (byte : { byte : UInt8 // byte ∉ EfficientMmtDuplicativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfficientMmtDuplicativeIndicator

def toByte : EfficientMmtDuplicativeIndicator → UInt8
  | .dupl => 0x31
  | .uniqueTradeReport => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfficientMmtDuplicativeIndicator :=
  if byte = 0x31 then .dupl
  else .uniqueTradeReport

def ofByte (byte : UInt8) : EfficientMmtDuplicativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfficientMmtDuplicativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | dupl => decide
  | uniqueTradeReport => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfficientMmtDuplicativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfficientMmtDuplicativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfficientMmtDuplicativeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EfficientMmtDuplicativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfficientMmtDuplicativeIndicator

/-- Opened Closed Fund: one byte code -/
def OpenedClosedFund.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenedClosedFund where
  | open_ -- Open
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenedClosedFund.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenedClosedFund

def toByte : OpenedClosedFund → UInt8
  | .open_ => 0x4F
  | .closed => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenedClosedFund :=
  if byte = 0x4F then .open_
  else .closed

def ofByte (byte : UInt8) : OpenedClosedFund :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenedClosedFund) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenedClosedFund) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenedClosedFund × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenedClosedFund) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenedClosedFund) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenedClosedFund

/-- Gross Of Cdsc Indicator: one byte code -/
def GrossOfCdscIndicator.codes : List UInt8 :=
  [0x4E, 0x59]

inductive GrossOfCdscIndicator where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ GrossOfCdscIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GrossOfCdscIndicator

def toByte : GrossOfCdscIndicator → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GrossOfCdscIndicator :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : GrossOfCdscIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GrossOfCdscIndicator) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GrossOfCdscIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GrossOfCdscIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GrossOfCdscIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : GrossOfCdscIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GrossOfCdscIndicator

/-- Tax Description Attaching To A Dividend: one byte code -/
def TaxDescriptionAttachingToADividend.codes : List UInt8 :=
  [0x44]

inductive TaxDescriptionAttachingToADividend where
  | deducedatSource -- Deducedat Source
  | unlisted (byte : { byte : UInt8 // byte ∉ TaxDescriptionAttachingToADividend.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TaxDescriptionAttachingToADividend

def toByte : TaxDescriptionAttachingToADividend → UInt8
  | .deducedatSource => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TaxDescriptionAttachingToADividend :=
  .deducedatSource

def ofByte (byte : UInt8) : TaxDescriptionAttachingToADividend :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TaxDescriptionAttachingToADividend) : ofByte value.toByte = value := by
  cases value with
  | deducedatSource => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TaxDescriptionAttachingToADividend) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TaxDescriptionAttachingToADividend × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TaxDescriptionAttachingToADividend) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TaxDescriptionAttachingToADividend) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TaxDescriptionAttachingToADividend

/-- Security Condition: one byte code -/
def SecurityCondition.codes : List UInt8 :=
  [0x4F, 0x44, 0x43, 0x52, 0x45, 0x53, 0x4E]

inductive SecurityCondition where
  | normal -- Normal
  | exDividend -- Ex Dividend
  | exCap -- Ex Cap
  | exRights -- Ex Rights
  | exEntitlement -- Ex Entitlement
  | dealingstemporarilysuspended -- Dealingstemporarilysuspended
  | notListed -- Not Listed
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityCondition

def toByte : SecurityCondition → UInt8
  | .normal => 0x4F
  | .exDividend => 0x44
  | .exCap => 0x43
  | .exRights => 0x52
  | .exEntitlement => 0x45
  | .dealingstemporarilysuspended => 0x53
  | .notListed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityCondition :=
  if byte = 0x4F then .normal
  else if byte = 0x44 then .exDividend
  else if byte = 0x43 then .exCap
  else if byte = 0x52 then .exRights
  else if byte = 0x45 then .exEntitlement
  else if byte = 0x53 then .dealingstemporarilysuspended
  else .notListed

def ofByte (byte : UInt8) : SecurityCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityCondition) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | exDividend => decide
  | exCap => decide
  | exRights => decide
  | exEntitlement => decide
  | dealingstemporarilysuspended => decide
  | notListed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityCondition

/-- Start Of Day Message: 10 bytes -/
structure StartOfDayMessage where
  mdSeqNum : BitVec 64
  sessionTradingDay : BitVec 16
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUIntLE 2 message.sessionTradingDay)

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (sessionTradingDay, bytes) ← decodeUIntLE 2 bytes
  pure ({ mdSeqNum, sessionTradingDay }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StartOfDayMessage

/-- End Of Day Message: 10 bytes -/
structure EndOfDayMessage where
  mdSeqNum : BitVec 64
  sessionTradingDay : BitVec 16
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUIntLE 2 message.sessionTradingDay)

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (sessionTradingDay, bytes) ← decodeUIntLE 2 bytes
  pure ({ mdSeqNum, sessionTradingDay }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EndOfDayMessage

/-- Health Status Message: 16 bytes -/
structure HealthStatusMessage where
  mdSeqNum : BitVec 64
  eventTime : BitVec 64
  deriving DecidableEq, Repr

namespace HealthStatusMessage

def encode (message : HealthStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUIntLE 8 message.eventTime)

def decode (bytes : List UInt8) : Option (HealthStatusMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdSeqNum, eventTime }, bytes)

@[simp] theorem encode_length (message : HealthStatusMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : HealthStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HealthStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HealthStatusMessage

/-- Technical Notification Message: 30 bytes -/
structure TechnicalNotificationMessage where
  mdSeqNumOptional : BitVec 64
  technicalNotificationType : BitVec 8
  rebroadcastIndicator : BitVec 8
  retransmissionStartTime : BitVec 64
  retransmissionEndTime : BitVec 64
  symbolIndexOptional : BitVec 32
  deriving DecidableEq, Repr

namespace TechnicalNotificationMessage

def encode (message : TechnicalNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.technicalNotificationType
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 8 message.retransmissionStartTime
    ++ (encodeUIntLE 8 message.retransmissionEndTime
    ++ (encodeUIntLE 4 message.symbolIndexOptional)))))

def decode (bytes : List UInt8) : Option (TechnicalNotificationMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (technicalNotificationType, bytes) ← decodeUInt 1 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (retransmissionStartTime, bytes) ← decodeUIntLE 8 bytes
  let (retransmissionEndTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  pure ({ mdSeqNumOptional, technicalNotificationType, rebroadcastIndicator, retransmissionStartTime, retransmissionEndTime, symbolIndexOptional }, bytes)

@[simp] theorem encode_length (message : TechnicalNotificationMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TechnicalNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TechnicalNotificationMessage

/-- Market Updates Group: 23 bytes -/
structure MarketUpdatesGroup where
  updateType : BitVec 8
  symbolIndex : BitVec 32
  numberOfOrders : BitVec 16
  price : BitVec 64
  quantityOptional : BitVec 64
  deriving DecidableEq, Repr

namespace MarketUpdatesGroup

def encode (message : MarketUpdatesGroup) : List UInt8 :=
  encodeUInt 1 message.updateType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 2 message.numberOfOrders
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantityOptional))))

def decode (bytes : List UInt8) : Option (MarketUpdatesGroup × List UInt8) := do
  let (updateType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  pure ({ updateType, symbolIndex, numberOfOrders, price, quantityOptional }, bytes)

@[simp] theorem encode_length (message : MarketUpdatesGroup) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketUpdatesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketUpdatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketUpdatesGroup

/-- Market Updates Groups -/
structure MarketUpdatesGroups where
  blockLengthShort : BitVec 8
  marketUpdatesGroup : Bounded 1 MarketUpdatesGroup
  deriving DecidableEq, Repr

namespace MarketUpdatesGroups

def encode (message : MarketUpdatesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketUpdatesGroup.val.length)
    ++ (encodeMany MarketUpdatesGroup.encode message.marketUpdatesGroup.val))

def decode (bytes : List UInt8) : Option (MarketUpdatesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketUpdatesGroup_, bytes) ← decodeMany MarketUpdatesGroup.decode numInGroup.toNat bytes
  if fits_marketUpdatesGroup : marketUpdatesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, marketUpdatesGroup := ⟨marketUpdatesGroup_, fits_marketUpdatesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketUpdatesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketUpdatesGroups) : (encode message).length ≤ 5867 := by
  have bound_marketUpdatesGroup := message.marketUpdatesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const MarketUpdatesGroup.encode 23 MarketUpdatesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketUpdatesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketUpdatesGroup.encode MarketUpdatesGroup.decode MarketUpdatesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketUpdatesGroup.length_lt]
  rfl

end MarketUpdatesGroups

/-- Market Update Message -/
structure MarketUpdateMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  marketUpdatesGroups : MarketUpdatesGroups
  deriving DecidableEq, Repr

namespace MarketUpdateMessage

def encode (message : MarketUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (MarketUpdatesGroups.encode message.marketUpdatesGroups))))

def decode (bytes : List UInt8) : Option (MarketUpdateMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (marketUpdatesGroups, bytes) ← MarketUpdatesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, marketUpdatesGroups }, bytes)

theorem encode_length_pos (message : MarketUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketUpdateMessage) : (encode message).length ≤ 5885 := by
  have bound_marketUpdatesGroups := MarketUpdatesGroups.encode_length_le message.marketUpdatesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MarketUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MarketUpdatesGroups.decode_encode, some_bind]
  rfl

end MarketUpdateMessage

/-- Order Updates Group: 40 bytes -/
structure OrderUpdatesGroup where
  symbolIndex : BitVec 32
  actionType : BitVec 8
  orderPriority : BitVec 64
  previousPriority : BitVec 64
  orderType : BitVec 8
  orderPx : BitVec 64
  orderSide : BitVec 8
  orderQuantity : BitVec 64
  pegOffset : BitVec 8
  deriving DecidableEq, Repr

namespace OrderUpdatesGroup

def encode (message : OrderUpdatesGroup) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.actionType
    ++ (encodeUIntLE 8 message.orderPriority
    ++ (encodeUIntLE 8 message.previousPriority
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUInt 1 message.orderSide
    ++ (encodeUIntLE 8 message.orderQuantity
    ++ (encodeUInt 1 message.pegOffset))))))))

def decode (bytes : List UInt8) : Option (OrderUpdatesGroup × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (actionType, bytes) ← decodeUInt 1 bytes
  let (orderPriority, bytes) ← decodeUIntLE 8 bytes
  let (previousPriority, bytes) ← decodeUIntLE 8 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (orderQuantity, bytes) ← decodeUIntLE 8 bytes
  let (pegOffset, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, actionType, orderPriority, previousPriority, orderType, orderPx, orderSide, orderQuantity, pegOffset }, bytes)

@[simp] theorem encode_length (message : OrderUpdatesGroup) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderUpdatesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderUpdatesGroup

/-- Order Updates Groups -/
structure OrderUpdatesGroups where
  blockLengthShort : BitVec 8
  orderUpdatesGroup : Bounded 1 OrderUpdatesGroup
  deriving DecidableEq, Repr

namespace OrderUpdatesGroups

def encode (message : OrderUpdatesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderUpdatesGroup.val.length)
    ++ (encodeMany OrderUpdatesGroup.encode message.orderUpdatesGroup.val))

def decode (bytes : List UInt8) : Option (OrderUpdatesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (orderUpdatesGroup_, bytes) ← decodeMany OrderUpdatesGroup.decode numInGroup.toNat bytes
  if fits_orderUpdatesGroup : orderUpdatesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, orderUpdatesGroup := ⟨orderUpdatesGroup_, fits_orderUpdatesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderUpdatesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderUpdatesGroups) : (encode message).length ≤ 10202 := by
  have bound_orderUpdatesGroup := message.orderUpdatesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const OrderUpdatesGroup.encode 40 OrderUpdatesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderUpdatesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderUpdatesGroup.encode OrderUpdatesGroup.decode OrderUpdatesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderUpdatesGroup.length_lt]
  rfl

end OrderUpdatesGroups

/-- Order Update Message -/
structure OrderUpdateMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  orderUpdatesGroups : OrderUpdatesGroups
  deriving DecidableEq, Repr

namespace OrderUpdateMessage

def encode (message : OrderUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (OrderUpdatesGroups.encode message.orderUpdatesGroups))))

def decode (bytes : List UInt8) : Option (OrderUpdateMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (orderUpdatesGroups, bytes) ← OrderUpdatesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, orderUpdatesGroups }, bytes)

theorem encode_length_pos (message : OrderUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderUpdateMessage) : (encode message).length ≤ 10220 := by
  have bound_orderUpdatesGroups := OrderUpdatesGroups.encode_length_le message.orderUpdatesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : OrderUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OrderUpdatesGroups.decode_encode, some_bind]
  rfl

end OrderUpdateMessage

/-- Price Updates Group: 31 bytes -/
structure PriceUpdatesGroup where
  priceType : BitVec 8
  symbolIndex : BitVec 32
  price : BitVec 64
  quantityOptional : BitVec 64
  imbalanceQty : BitVec 64
  imbalanceQtySide : BitVec 8
  priceQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace PriceUpdatesGroup

def encode (message : PriceUpdatesGroup) : List UInt8 :=
  encodeUInt 1 message.priceType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantityOptional
    ++ (encodeUIntLE 8 message.imbalanceQty
    ++ (encodeUInt 1 message.imbalanceQtySide
    ++ (encodeUInt 1 message.priceQualifier))))))

def decode (bytes : List UInt8) : Option (PriceUpdatesGroup × List UInt8) := do
  let (priceType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQty, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQtySide, bytes) ← decodeUInt 1 bytes
  let (priceQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ priceType, symbolIndex, price, quantityOptional, imbalanceQty, imbalanceQtySide, priceQualifier }, bytes)

@[simp] theorem encode_length (message : PriceUpdatesGroup) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : PriceUpdatesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceUpdatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceUpdatesGroup

/-- Price Updates Groups -/
structure PriceUpdatesGroups where
  blockLengthShort : BitVec 8
  priceUpdatesGroup : Bounded 1 PriceUpdatesGroup
  deriving DecidableEq, Repr

namespace PriceUpdatesGroups

def encode (message : PriceUpdatesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.priceUpdatesGroup.val.length)
    ++ (encodeMany PriceUpdatesGroup.encode message.priceUpdatesGroup.val))

def decode (bytes : List UInt8) : Option (PriceUpdatesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (priceUpdatesGroup_, bytes) ← decodeMany PriceUpdatesGroup.decode numInGroup.toNat bytes
  if fits_priceUpdatesGroup : priceUpdatesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, priceUpdatesGroup := ⟨priceUpdatesGroup_, fits_priceUpdatesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PriceUpdatesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceUpdatesGroups) : (encode message).length ≤ 7907 := by
  have bound_priceUpdatesGroup := message.priceUpdatesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const PriceUpdatesGroup.encode 31 PriceUpdatesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PriceUpdatesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PriceUpdatesGroup.encode PriceUpdatesGroup.decode PriceUpdatesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.priceUpdatesGroup.length_lt]
  rfl

end PriceUpdatesGroups

/-- Price Update Message -/
structure PriceUpdateMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  priceUpdatesGroups : PriceUpdatesGroups
  deriving DecidableEq, Repr

namespace PriceUpdateMessage

def encode (message : PriceUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (PriceUpdatesGroups.encode message.priceUpdatesGroups))))

def decode (bytes : List UInt8) : Option (PriceUpdateMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (priceUpdatesGroups, bytes) ← PriceUpdatesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, priceUpdatesGroups }, bytes)

theorem encode_length_pos (message : PriceUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceUpdateMessage) : (encode message).length ≤ 7925 := by
  have bound_priceUpdatesGroups := PriceUpdatesGroups.encode_length_le message.priceUpdatesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : PriceUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PriceUpdatesGroups.decode_encode, some_bind]
  rfl

end PriceUpdateMessage

/-- Not Used Groups: 2 bytes -/
structure NotUsedGroups where
  blockLengthShort : BitVec 8
  numInGroup : BitVec 8
  deriving DecidableEq, Repr

namespace NotUsedGroups

def encode (message : NotUsedGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 message.numInGroup)

def decode (bytes : List UInt8) : Option (NotUsedGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  pure ({ blockLengthShort, numInGroup }, bytes)

@[simp] theorem encode_length (message : NotUsedGroups) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : NotUsedGroups) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotUsedGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NotUsedGroups

/-- Full Trade Information Message: 422 bytes -/
structure FullTradeInformationMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  symbolIndexOptional : BitVec 32
  tradingDateTime : Alpha 27
  publicationDateTime : Alpha 27
  tradeType : BitVec 8
  mifidInstrumentIdTypeOptional : Alpha 4
  mifidInstrumentIdOptional : Alpha 12
  mifidExecutionId : Alpha 52
  mifidPriceOptional : Alpha 20
  mifidQuantity : Alpha 20
  mifidPriceNotation : Alpha 4
  mifidCurrency : Alpha 3
  mifidQtyInMsrmtUnitNotation : Alpha 25
  mifidQuantityMeasurementUnit : Alpha 20
  mifidNotionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  mifidClearingFlag : Alpha 5
  mmtMarketMechanism : BitVec 8
  mmtTradingMode : MmtTradingMode
  mmtTransactionCategory : Alpha 4
  mmtNegotiationIndicator : Alpha 4
  mmtAgencyCrossTradeIndicator : Alpha 4
  mmtModificationIndicatorOptional : Alpha 4
  mmtBenchmarkIndicator : Alpha 4
  mmtSpecialDividendIndicator : Alpha 4
  mmtOffBookAutomatedIndicator : MmtOffBookAutomatedIndicator
  mmtContributiontoPrice : Alpha 4
  mmtAlgorithmicIndicator : Alpha 4
  mmtPublicationMode : Alpha 4
  mmtPostTradeDeferral : Alpha 4
  mmtDuplicativeIndicator : Alpha 4
  tradeQualifier : BitVec 8
  transactionType : BitVec 8
  effectiveDateIndicator : BitVec 8
  blockTradeCode : BlockTradeCode
  tradeReference : Alpha 30
  originalReportTimestamp : BitVec 64
  transparencyIndicator : BitVec 8
  currencyCoefficient : BitVec 32
  priceMultiplier : BitVec 32
  priceMultiplierDecimals : BitVec 8
  venue : Alpha 11
  startTimeVwap : BitVec 32
  endTimeVwap : BitVec 32
  mifidEmissionAllowanceType : Alpha 4
  marketOfReferenceMic : Alpha 4
  evaluatedPrice : BitVec 64
  messagePriceNotation : BitVec 8
  settlementDate : BitVec 16
  repoSettlementDate : BitVec 16
  tradeUniqueIdentifier : Alpha 16
  notUsedGroups : NotUsedGroups
  deriving DecidableEq, Repr

namespace FullTradeInformationMessage

def encode (message : FullTradeInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (Alpha.encode message.tradingDateTime
    ++ (Alpha.encode message.publicationDateTime
    ++ (encodeUInt 1 message.tradeType
    ++ (Alpha.encode message.mifidInstrumentIdTypeOptional
    ++ (Alpha.encode message.mifidInstrumentIdOptional
    ++ (Alpha.encode message.mifidExecutionId
    ++ (Alpha.encode message.mifidPriceOptional
    ++ (Alpha.encode message.mifidQuantity
    ++ (Alpha.encode message.mifidPriceNotation
    ++ (Alpha.encode message.mifidCurrency
    ++ (Alpha.encode message.mifidQtyInMsrmtUnitNotation
    ++ (Alpha.encode message.mifidQuantityMeasurementUnit
    ++ (Alpha.encode message.mifidNotionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.mifidClearingFlag
    ++ (encodeUInt 1 message.mmtMarketMechanism
    ++ (MmtTradingMode.encode message.mmtTradingMode
    ++ (Alpha.encode message.mmtTransactionCategory
    ++ (Alpha.encode message.mmtNegotiationIndicator
    ++ (Alpha.encode message.mmtAgencyCrossTradeIndicator
    ++ (Alpha.encode message.mmtModificationIndicatorOptional
    ++ (Alpha.encode message.mmtBenchmarkIndicator
    ++ (Alpha.encode message.mmtSpecialDividendIndicator
    ++ (MmtOffBookAutomatedIndicator.encode message.mmtOffBookAutomatedIndicator
    ++ (Alpha.encode message.mmtContributiontoPrice
    ++ (Alpha.encode message.mmtAlgorithmicIndicator
    ++ (Alpha.encode message.mmtPublicationMode
    ++ (Alpha.encode message.mmtPostTradeDeferral
    ++ (Alpha.encode message.mmtDuplicativeIndicator
    ++ (encodeUIntLE 1 message.tradeQualifier
    ++ (encodeUInt 1 message.transactionType
    ++ (encodeUInt 1 message.effectiveDateIndicator
    ++ (BlockTradeCode.encode message.blockTradeCode
    ++ (Alpha.encode message.tradeReference
    ++ (encodeUIntLE 8 message.originalReportTimestamp
    ++ (encodeUInt 1 message.transparencyIndicator
    ++ (encodeUIntLE 4 message.currencyCoefficient
    ++ (encodeUIntLE 4 message.priceMultiplier
    ++ (encodeUInt 1 message.priceMultiplierDecimals
    ++ (Alpha.encode message.venue
    ++ (encodeUIntLE 4 message.startTimeVwap
    ++ (encodeUIntLE 4 message.endTimeVwap
    ++ (Alpha.encode message.mifidEmissionAllowanceType
    ++ (Alpha.encode message.marketOfReferenceMic
    ++ (encodeUIntLE 8 message.evaluatedPrice
    ++ (encodeUInt 1 message.messagePriceNotation
    ++ (encodeUIntLE 2 message.settlementDate
    ++ (encodeUIntLE 2 message.repoSettlementDate
    ++ (Alpha.encode message.tradeUniqueIdentifier
    ++ (NotUsedGroups.encode message.notUsedGroups))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FullTradeInformationMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradingDateTime, bytes) ← Alpha.decode 27 bytes
  let (publicationDateTime, bytes) ← Alpha.decode 27 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (mifidInstrumentIdTypeOptional, bytes) ← Alpha.decode 4 bytes
  let (mifidInstrumentIdOptional, bytes) ← Alpha.decode 12 bytes
  let (mifidExecutionId, bytes) ← Alpha.decode 52 bytes
  let (mifidPriceOptional, bytes) ← Alpha.decode 20 bytes
  let (mifidQuantity, bytes) ← Alpha.decode 20 bytes
  let (mifidPriceNotation, bytes) ← Alpha.decode 4 bytes
  let (mifidCurrency, bytes) ← Alpha.decode 3 bytes
  let (mifidQtyInMsrmtUnitNotation, bytes) ← Alpha.decode 25 bytes
  let (mifidQuantityMeasurementUnit, bytes) ← Alpha.decode 20 bytes
  let (mifidNotionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (mifidClearingFlag, bytes) ← Alpha.decode 5 bytes
  let (mmtMarketMechanism, bytes) ← decodeUInt 1 bytes
  let (mmtTradingMode, bytes) ← MmtTradingMode.decode bytes
  let (mmtTransactionCategory, bytes) ← Alpha.decode 4 bytes
  let (mmtNegotiationIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtAgencyCrossTradeIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtModificationIndicatorOptional, bytes) ← Alpha.decode 4 bytes
  let (mmtBenchmarkIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtSpecialDividendIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtOffBookAutomatedIndicator, bytes) ← MmtOffBookAutomatedIndicator.decode bytes
  let (mmtContributiontoPrice, bytes) ← Alpha.decode 4 bytes
  let (mmtAlgorithmicIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtPublicationMode, bytes) ← Alpha.decode 4 bytes
  let (mmtPostTradeDeferral, bytes) ← Alpha.decode 4 bytes
  let (mmtDuplicativeIndicator, bytes) ← Alpha.decode 4 bytes
  let (tradeQualifier, bytes) ← decodeUIntLE 1 bytes
  let (transactionType, bytes) ← decodeUInt 1 bytes
  let (effectiveDateIndicator, bytes) ← decodeUInt 1 bytes
  let (blockTradeCode, bytes) ← BlockTradeCode.decode bytes
  let (tradeReference, bytes) ← Alpha.decode 30 bytes
  let (originalReportTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (transparencyIndicator, bytes) ← decodeUInt 1 bytes
  let (currencyCoefficient, bytes) ← decodeUIntLE 4 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (priceMultiplierDecimals, bytes) ← decodeUInt 1 bytes
  let (venue, bytes) ← Alpha.decode 11 bytes
  let (startTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (endTimeVwap, bytes) ← decodeUIntLE 4 bytes
  let (mifidEmissionAllowanceType, bytes) ← Alpha.decode 4 bytes
  let (marketOfReferenceMic, bytes) ← Alpha.decode 4 bytes
  let (evaluatedPrice, bytes) ← decodeUIntLE 8 bytes
  let (messagePriceNotation, bytes) ← decodeUInt 1 bytes
  let (settlementDate, bytes) ← decodeUIntLE 2 bytes
  let (repoSettlementDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  let (notUsedGroups, bytes) ← NotUsedGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, symbolIndexOptional, tradingDateTime, publicationDateTime, tradeType, mifidInstrumentIdTypeOptional, mifidInstrumentIdOptional, mifidExecutionId, mifidPriceOptional, mifidQuantity, mifidPriceNotation, mifidCurrency, mifidQtyInMsrmtUnitNotation, mifidQuantityMeasurementUnit, mifidNotionalAmount, notionalCurrency, mifidClearingFlag, mmtMarketMechanism, mmtTradingMode, mmtTransactionCategory, mmtNegotiationIndicator, mmtAgencyCrossTradeIndicator, mmtModificationIndicatorOptional, mmtBenchmarkIndicator, mmtSpecialDividendIndicator, mmtOffBookAutomatedIndicator, mmtContributiontoPrice, mmtAlgorithmicIndicator, mmtPublicationMode, mmtPostTradeDeferral, mmtDuplicativeIndicator, tradeQualifier, transactionType, effectiveDateIndicator, blockTradeCode, tradeReference, originalReportTimestamp, transparencyIndicator, currencyCoefficient, priceMultiplier, priceMultiplierDecimals, venue, startTimeVwap, endTimeVwap, mifidEmissionAllowanceType, marketOfReferenceMic, evaluatedPrice, messagePriceNotation, settlementDate, repoSettlementDate, tradeUniqueIdentifier, notUsedGroups }, bytes)

@[simp] theorem encode_length (message : FullTradeInformationMessage) : (encode message).length = 422 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, MmtTradingMode.encode_length, MmtOffBookAutomatedIndicator.encode_length, BlockTradeCode.encode_length, NotUsedGroups.encode_length]

theorem encode_length_pos (message : FullTradeInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FullTradeInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MmtTradingMode.decode_encode, some_bind]
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
  rw [List.append_assoc, MmtOffBookAutomatedIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BlockTradeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotUsedGroups.decode_encode, some_bind]
  rfl

end FullTradeInformationMessage

/-- Market States Group: 33 bytes -/
structure MarketStatesGroup where
  changeType : BitVec 8
  symbolIndex : BitVec 32
  eventTime : BitVec 64
  bookState : BitVec 8
  statusReason : BitVec 8
  phaseQualifier : BitVec 16
  tradingPeriodOptional : BitVec 8
  tradingSide : BitVec 8
  priceLimits : BitVec 8
  quoteSpreadMultiplier : BitVec 8
  orderEntryQualifier : BitVec 8
  session : BitVec 8
  scheduledEvent : BitVec 8
  scheduledEventTime : BitVec 64
  instrumentState : BitVec 8
  deriving DecidableEq, Repr

namespace MarketStatesGroup

def encode (message : MarketStatesGroup) : List UInt8 :=
  encodeUInt 1 message.changeType
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUInt 1 message.bookState
    ++ (encodeUInt 1 message.statusReason
    ++ (encodeUIntLE 2 message.phaseQualifier
    ++ (encodeUInt 1 message.tradingPeriodOptional
    ++ (encodeUInt 1 message.tradingSide
    ++ (encodeUInt 1 message.priceLimits
    ++ (encodeUInt 1 message.quoteSpreadMultiplier
    ++ (encodeUInt 1 message.orderEntryQualifier
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 1 message.scheduledEvent
    ++ (encodeUIntLE 8 message.scheduledEventTime
    ++ (encodeUInt 1 message.instrumentState))))))))))))))

def decode (bytes : List UInt8) : Option (MarketStatesGroup × List UInt8) := do
  let (changeType, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (bookState, bytes) ← decodeUInt 1 bytes
  let (statusReason, bytes) ← decodeUInt 1 bytes
  let (phaseQualifier, bytes) ← decodeUIntLE 2 bytes
  let (tradingPeriodOptional, bytes) ← decodeUInt 1 bytes
  let (tradingSide, bytes) ← decodeUInt 1 bytes
  let (priceLimits, bytes) ← decodeUInt 1 bytes
  let (quoteSpreadMultiplier, bytes) ← decodeUInt 1 bytes
  let (orderEntryQualifier, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (scheduledEvent, bytes) ← decodeUInt 1 bytes
  let (scheduledEventTime, bytes) ← decodeUIntLE 8 bytes
  let (instrumentState, bytes) ← decodeUInt 1 bytes
  pure ({ changeType, symbolIndex, eventTime, bookState, statusReason, phaseQualifier, tradingPeriodOptional, tradingSide, priceLimits, quoteSpreadMultiplier, orderEntryQualifier, session, scheduledEvent, scheduledEventTime, instrumentState }, bytes)

@[simp] theorem encode_length (message : MarketStatesGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketStatesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketStatesGroup

/-- Market States Groups -/
structure MarketStatesGroups where
  blockLengthShort : BitVec 8
  marketStatesGroup : Bounded 1 MarketStatesGroup
  deriving DecidableEq, Repr

namespace MarketStatesGroups

def encode (message : MarketStatesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketStatesGroup.val.length)
    ++ (encodeMany MarketStatesGroup.encode message.marketStatesGroup.val))

def decode (bytes : List UInt8) : Option (MarketStatesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketStatesGroup_, bytes) ← decodeMany MarketStatesGroup.decode numInGroup.toNat bytes
  if fits_marketStatesGroup : marketStatesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, marketStatesGroup := ⟨marketStatesGroup_, fits_marketStatesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketStatesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatesGroups) : (encode message).length ≤ 8417 := by
  have bound_marketStatesGroup := message.marketStatesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const MarketStatesGroup.encode 33 MarketStatesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketStatesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketStatesGroup.encode MarketStatesGroup.decode MarketStatesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketStatesGroup.length_lt]
  rfl

end MarketStatesGroups

/-- Market Status Change Message -/
structure MarketStatusChangeMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  marketStatesGroups : MarketStatesGroups
  deriving DecidableEq, Repr

namespace MarketStatusChangeMessage

def encode (message : MarketStatusChangeMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (MarketStatesGroups.encode message.marketStatesGroups)))

def decode (bytes : List UInt8) : Option (MarketStatusChangeMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (marketStatesGroups, bytes) ← MarketStatesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, marketStatesGroups }, bytes)

theorem encode_length_pos (message : MarketStatusChangeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatusChangeMessage) : (encode message).length ≤ 8427 := by
  have bound_marketStatesGroups := MarketStatesGroups.encode_length_le message.marketStatesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MarketStatusChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MarketStatesGroups.decode_encode, some_bind]
  rfl

end MarketStatusChangeMessage

/-- Timetables Group: 15 bytes -/
structure TimetablesGroup where
  phaseTime : BitVec 64
  phaseId : BitVec 8
  phaseQualifier : BitVec 16
  tradingPeriod : BitVec 8
  orderEntryQualifier : BitVec 8
  session : BitVec 8
  scheduledEvent : BitVec 8
  deriving DecidableEq, Repr

namespace TimetablesGroup

def encode (message : TimetablesGroup) : List UInt8 :=
  encodeUIntLE 8 message.phaseTime
    ++ (encodeUInt 1 message.phaseId
    ++ (encodeUIntLE 2 message.phaseQualifier
    ++ (encodeUInt 1 message.tradingPeriod
    ++ (encodeUInt 1 message.orderEntryQualifier
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 1 message.scheduledEvent))))))

def decode (bytes : List UInt8) : Option (TimetablesGroup × List UInt8) := do
  let (phaseTime, bytes) ← decodeUIntLE 8 bytes
  let (phaseId, bytes) ← decodeUInt 1 bytes
  let (phaseQualifier, bytes) ← decodeUIntLE 2 bytes
  let (tradingPeriod, bytes) ← decodeUInt 1 bytes
  let (orderEntryQualifier, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (scheduledEvent, bytes) ← decodeUInt 1 bytes
  pure ({ phaseTime, phaseId, phaseQualifier, tradingPeriod, orderEntryQualifier, session, scheduledEvent }, bytes)

@[simp] theorem encode_length (message : TimetablesGroup) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TimetablesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimetablesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimetablesGroup

/-- Timetables Groups -/
structure TimetablesGroups where
  blockLengthShort : BitVec 8
  timetablesGroup : Bounded 1 TimetablesGroup
  deriving DecidableEq, Repr

namespace TimetablesGroups

def encode (message : TimetablesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.timetablesGroup.val.length)
    ++ (encodeMany TimetablesGroup.encode message.timetablesGroup.val))

def decode (bytes : List UInt8) : Option (TimetablesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (timetablesGroup_, bytes) ← decodeMany TimetablesGroup.decode numInGroup.toNat bytes
  if fits_timetablesGroup : timetablesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, timetablesGroup := ⟨timetablesGroup_, fits_timetablesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TimetablesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TimetablesGroups) : (encode message).length ≤ 3827 := by
  have bound_timetablesGroup := message.timetablesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const TimetablesGroup.encode 15 TimetablesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TimetablesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TimetablesGroup.encode TimetablesGroup.decode TimetablesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.timetablesGroup.length_lt]
  rfl

end TimetablesGroups

/-- Timetable Message -/
structure TimetableMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emmOptional : BitVec 8
  patternId : BitVec 16
  symbolIndexOptional : BitVec 32
  timetablesGroups : TimetablesGroups
  deriving DecidableEq, Repr

namespace TimetableMessage

def encode (message : TimetableMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emmOptional
    ++ (encodeUIntLE 2 message.patternId
    ++ (encodeUIntLE 4 message.symbolIndexOptional
    ++ (TimetablesGroups.encode message.timetablesGroups)))))

def decode (bytes : List UInt8) : Option (TimetableMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (patternId, bytes) ← decodeUIntLE 2 bytes
  let (symbolIndexOptional, bytes) ← decodeUIntLE 4 bytes
  let (timetablesGroups, bytes) ← TimetablesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emmOptional, patternId, symbolIndexOptional, timetablesGroups }, bytes)

theorem encode_length_pos (message : TimetableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TimetableMessage) : (encode message).length ≤ 3843 := by
  have bound_timetablesGroups := TimetablesGroups.encode_length_le message.timetablesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : TimetableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TimetablesGroups.decode_encode, some_bind]
  rfl

end TimetableMessage

/-- Emm Pattern Rep Group: 16 bytes -/
structure EmmPatternRepGroup where
  emm : BitVec 8
  patternId : BitVec 16
  tickSizeIndexId : BitVec 16
  marketModel : BitVec 8
  lotSizeOptional : BitVec 64
  instUnitExp : BitVec 8
  anonymous : BitVec 8
  deriving DecidableEq, Repr

namespace EmmPatternRepGroup

def encode (message : EmmPatternRepGroup) : List UInt8 :=
  encodeUInt 1 message.emm
    ++ (encodeUIntLE 2 message.patternId
    ++ (encodeUIntLE 2 message.tickSizeIndexId
    ++ (encodeUInt 1 message.marketModel
    ++ (encodeUIntLE 8 message.lotSizeOptional
    ++ (encodeUInt 1 message.instUnitExp
    ++ (encodeUInt 1 message.anonymous))))))

def decode (bytes : List UInt8) : Option (EmmPatternRepGroup × List UInt8) := do
  let (emm, bytes) ← decodeUInt 1 bytes
  let (patternId, bytes) ← decodeUIntLE 2 bytes
  let (tickSizeIndexId, bytes) ← decodeUIntLE 2 bytes
  let (marketModel, bytes) ← decodeUInt 1 bytes
  let (lotSizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (instUnitExp, bytes) ← decodeUInt 1 bytes
  let (anonymous, bytes) ← decodeUInt 1 bytes
  pure ({ emm, patternId, tickSizeIndexId, marketModel, lotSizeOptional, instUnitExp, anonymous }, bytes)

@[simp] theorem encode_length (message : EmmPatternRepGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : EmmPatternRepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EmmPatternRepGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EmmPatternRepGroup

/-- Emm Pattern Rep Groups -/
structure EmmPatternRepGroups where
  blockLengthShort : BitVec 8
  emmPatternRepGroup : Bounded 1 EmmPatternRepGroup
  deriving DecidableEq, Repr

namespace EmmPatternRepGroups

def encode (message : EmmPatternRepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.emmPatternRepGroup.val.length)
    ++ (encodeMany EmmPatternRepGroup.encode message.emmPatternRepGroup.val))

def decode (bytes : List UInt8) : Option (EmmPatternRepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (emmPatternRepGroup_, bytes) ← decodeMany EmmPatternRepGroup.decode numInGroup.toNat bytes
  if fits_emmPatternRepGroup : emmPatternRepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, emmPatternRepGroup := ⟨emmPatternRepGroup_, fits_emmPatternRepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : EmmPatternRepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EmmPatternRepGroups) : (encode message).length ≤ 4082 := by
  have bound_emmPatternRepGroup := message.emmPatternRepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const EmmPatternRepGroup.encode 16 EmmPatternRepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : EmmPatternRepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 EmmPatternRepGroup.encode EmmPatternRepGroup.decode EmmPatternRepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.emmPatternRepGroup.length_lt]
  rfl

end EmmPatternRepGroups

/-- Standing Data Message -/
structure StandingDataMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  optiqSegment : BitVec 8
  partitionId : BitVec 16
  fullInstrumentName : Alpha 102
  instrumentName : Alpha 18
  instrumentTradingCode : Alpha 15
  instrumentGroupCode : Alpha 2
  isinCode : Alpha 12
  priceDecimals : BitVec 8
  quantityDecimals : BitVec 8
  amountDecimals : BitVec 8
  ratioDecimals : BitVec 8
  cfi : Alpha 6
  instrumentEventDate : BitVec 16
  strikePrice : BitVec 64
  darkEligibility : BitVec 8
  darkLisThreshold : BitVec 64
  darkMinQuantity : BitVec 32
  dateOfLastTrade : BitVec 16
  depositaryList : Alpha 20
  mainDepositary : Alpha 5
  firstSettlementDate : BitVec 16
  guaranteeIndicator : BitVec 8
  icb : Alpha 16
  issuingCountry : Alpha 3
  lastAdjustedClosingPrice : BitVec 64
  lotSizeOptional : BitVec 64
  maturityDateOptional : Alpha 8
  maximumDecimalsInQuantity : BitVec 8
  mic : Alpha 4
  micList : Alpha 20
  countryOfExchangeOptional : Alpha 3
  mnemonic : Alpha 5
  underlyingMic : Alpha 4
  underlyingIsinCode : Alpha 12
  tradingCurrencyOptional : Alpha 3
  currencyCoefficient : BitVec 32
  tradingCurrencyIndicator : BitVec 8
  strikeCurrencyIndicator : BitVec 8
  numberInstrumentCirculating : BitVec 64
  parValue : BitVec 64
  quantityNotation : Alpha 3
  instUnitExp : BitVec 8
  settlementDelay : Alpha 2
  strikeCurrency : Alpha 3
  taxCode : BitVec 8
  typeOfCorporateEvent : Alpha 2
  typeOfMarketAdmission : TypeOfMarketAdmission
  repoIndicator : BitVec 8
  issuePrice : BitVec 64
  nominalCurrency : Alpha 3
  issuePriceDecimals : BitVec 8
  strikePriceDecimals : BitVec 8
  liquidInstrumentIndicator : BitVec 8
  marketOfReferenceMic : Alpha 4
  icbCode : Alpha 8
  thresholdLisPostTrade60mn : BitVec 64
  thresholdLisPostTrade120mn : BitVec 64
  thresholdLisPostTradeEod : BitVec 64
  longMnemonic : Alpha 6
  maxOrderAmountCall : BitVec 64
  maxOrderAmountContinuous : BitVec 64
  maxOrderQuantityCall : BitVec 64
  maxOrderQuantityContinuous : BitVec 64
  poolFactor : BitVec 32
  emmPatternRepGroups : EmmPatternRepGroups
  deriving DecidableEq, Repr

namespace StandingDataMessage

def encode (message : StandingDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.optiqSegment
    ++ (encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.fullInstrumentName
    ++ (Alpha.encode message.instrumentName
    ++ (Alpha.encode message.instrumentTradingCode
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (Alpha.encode message.isinCode
    ++ (encodeUInt 1 message.priceDecimals
    ++ (encodeUInt 1 message.quantityDecimals
    ++ (encodeUInt 1 message.amountDecimals
    ++ (encodeUInt 1 message.ratioDecimals
    ++ (Alpha.encode message.cfi
    ++ (encodeUIntLE 2 message.instrumentEventDate
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUInt 1 message.darkEligibility
    ++ (encodeUIntLE 8 message.darkLisThreshold
    ++ (encodeUIntLE 4 message.darkMinQuantity
    ++ (encodeUIntLE 2 message.dateOfLastTrade
    ++ (Alpha.encode message.depositaryList
    ++ (Alpha.encode message.mainDepositary
    ++ (encodeUIntLE 2 message.firstSettlementDate
    ++ (encodeUInt 1 message.guaranteeIndicator
    ++ (Alpha.encode message.icb
    ++ (Alpha.encode message.issuingCountry
    ++ (encodeUIntLE 8 message.lastAdjustedClosingPrice
    ++ (encodeUIntLE 8 message.lotSizeOptional
    ++ (Alpha.encode message.maturityDateOptional
    ++ (encodeUInt 1 message.maximumDecimalsInQuantity
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.micList
    ++ (Alpha.encode message.countryOfExchangeOptional
    ++ (Alpha.encode message.mnemonic
    ++ (Alpha.encode message.underlyingMic
    ++ (Alpha.encode message.underlyingIsinCode
    ++ (Alpha.encode message.tradingCurrencyOptional
    ++ (encodeUIntLE 4 message.currencyCoefficient
    ++ (encodeUInt 1 message.tradingCurrencyIndicator
    ++ (encodeUInt 1 message.strikeCurrencyIndicator
    ++ (encodeUIntLE 8 message.numberInstrumentCirculating
    ++ (encodeUIntLE 8 message.parValue
    ++ (Alpha.encode message.quantityNotation
    ++ (encodeUInt 1 message.instUnitExp
    ++ (Alpha.encode message.settlementDelay
    ++ (Alpha.encode message.strikeCurrency
    ++ (encodeUInt 1 message.taxCode
    ++ (Alpha.encode message.typeOfCorporateEvent
    ++ (TypeOfMarketAdmission.encode message.typeOfMarketAdmission
    ++ (encodeUInt 1 message.repoIndicator
    ++ (encodeUIntLE 8 message.issuePrice
    ++ (Alpha.encode message.nominalCurrency
    ++ (encodeUInt 1 message.issuePriceDecimals
    ++ (encodeUInt 1 message.strikePriceDecimals
    ++ (encodeUInt 1 message.liquidInstrumentIndicator
    ++ (Alpha.encode message.marketOfReferenceMic
    ++ (Alpha.encode message.icbCode
    ++ (encodeUIntLE 8 message.thresholdLisPostTrade60mn
    ++ (encodeUIntLE 8 message.thresholdLisPostTrade120mn
    ++ (encodeUIntLE 8 message.thresholdLisPostTradeEod
    ++ (Alpha.encode message.longMnemonic
    ++ (encodeUIntLE 8 message.maxOrderAmountCall
    ++ (encodeUIntLE 8 message.maxOrderAmountContinuous
    ++ (encodeUIntLE 8 message.maxOrderQuantityCall
    ++ (encodeUIntLE 8 message.maxOrderQuantityContinuous
    ++ (encodeUIntLE 4 message.poolFactor
    ++ (EmmPatternRepGroups.encode message.emmPatternRepGroups)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (StandingDataMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (optiqSegment, bytes) ← decodeUInt 1 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (fullInstrumentName, bytes) ← Alpha.decode 102 bytes
  let (instrumentName, bytes) ← Alpha.decode 18 bytes
  let (instrumentTradingCode, bytes) ← Alpha.decode 15 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (priceDecimals, bytes) ← decodeUInt 1 bytes
  let (quantityDecimals, bytes) ← decodeUInt 1 bytes
  let (amountDecimals, bytes) ← decodeUInt 1 bytes
  let (ratioDecimals, bytes) ← decodeUInt 1 bytes
  let (cfi, bytes) ← Alpha.decode 6 bytes
  let (instrumentEventDate, bytes) ← decodeUIntLE 2 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (darkEligibility, bytes) ← decodeUInt 1 bytes
  let (darkLisThreshold, bytes) ← decodeUIntLE 8 bytes
  let (darkMinQuantity, bytes) ← decodeUIntLE 4 bytes
  let (dateOfLastTrade, bytes) ← decodeUIntLE 2 bytes
  let (depositaryList, bytes) ← Alpha.decode 20 bytes
  let (mainDepositary, bytes) ← Alpha.decode 5 bytes
  let (firstSettlementDate, bytes) ← decodeUIntLE 2 bytes
  let (guaranteeIndicator, bytes) ← decodeUInt 1 bytes
  let (icb, bytes) ← Alpha.decode 16 bytes
  let (issuingCountry, bytes) ← Alpha.decode 3 bytes
  let (lastAdjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (maturityDateOptional, bytes) ← Alpha.decode 8 bytes
  let (maximumDecimalsInQuantity, bytes) ← decodeUInt 1 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (micList, bytes) ← Alpha.decode 20 bytes
  let (countryOfExchangeOptional, bytes) ← Alpha.decode 3 bytes
  let (mnemonic, bytes) ← Alpha.decode 5 bytes
  let (underlyingMic, bytes) ← Alpha.decode 4 bytes
  let (underlyingIsinCode, bytes) ← Alpha.decode 12 bytes
  let (tradingCurrencyOptional, bytes) ← Alpha.decode 3 bytes
  let (currencyCoefficient, bytes) ← decodeUIntLE 4 bytes
  let (tradingCurrencyIndicator, bytes) ← decodeUInt 1 bytes
  let (strikeCurrencyIndicator, bytes) ← decodeUInt 1 bytes
  let (numberInstrumentCirculating, bytes) ← decodeUIntLE 8 bytes
  let (parValue, bytes) ← decodeUIntLE 8 bytes
  let (quantityNotation, bytes) ← Alpha.decode 3 bytes
  let (instUnitExp, bytes) ← decodeUInt 1 bytes
  let (settlementDelay, bytes) ← Alpha.decode 2 bytes
  let (strikeCurrency, bytes) ← Alpha.decode 3 bytes
  let (taxCode, bytes) ← decodeUInt 1 bytes
  let (typeOfCorporateEvent, bytes) ← Alpha.decode 2 bytes
  let (typeOfMarketAdmission, bytes) ← TypeOfMarketAdmission.decode bytes
  let (repoIndicator, bytes) ← decodeUInt 1 bytes
  let (issuePrice, bytes) ← decodeUIntLE 8 bytes
  let (nominalCurrency, bytes) ← Alpha.decode 3 bytes
  let (issuePriceDecimals, bytes) ← decodeUInt 1 bytes
  let (strikePriceDecimals, bytes) ← decodeUInt 1 bytes
  let (liquidInstrumentIndicator, bytes) ← decodeUInt 1 bytes
  let (marketOfReferenceMic, bytes) ← Alpha.decode 4 bytes
  let (icbCode, bytes) ← Alpha.decode 8 bytes
  let (thresholdLisPostTrade60mn, bytes) ← decodeUIntLE 8 bytes
  let (thresholdLisPostTrade120mn, bytes) ← decodeUIntLE 8 bytes
  let (thresholdLisPostTradeEod, bytes) ← decodeUIntLE 8 bytes
  let (longMnemonic, bytes) ← Alpha.decode 6 bytes
  let (maxOrderAmountCall, bytes) ← decodeUIntLE 8 bytes
  let (maxOrderAmountContinuous, bytes) ← decodeUIntLE 8 bytes
  let (maxOrderQuantityCall, bytes) ← decodeUIntLE 8 bytes
  let (maxOrderQuantityContinuous, bytes) ← decodeUIntLE 8 bytes
  let (poolFactor, bytes) ← decodeUIntLE 4 bytes
  let (emmPatternRepGroups, bytes) ← EmmPatternRepGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, symbolIndex, optiqSegment, partitionId, fullInstrumentName, instrumentName, instrumentTradingCode, instrumentGroupCode, isinCode, priceDecimals, quantityDecimals, amountDecimals, ratioDecimals, cfi, instrumentEventDate, strikePrice, darkEligibility, darkLisThreshold, darkMinQuantity, dateOfLastTrade, depositaryList, mainDepositary, firstSettlementDate, guaranteeIndicator, icb, issuingCountry, lastAdjustedClosingPrice, lotSizeOptional, maturityDateOptional, maximumDecimalsInQuantity, mic, micList, countryOfExchangeOptional, mnemonic, underlyingMic, underlyingIsinCode, tradingCurrencyOptional, currencyCoefficient, tradingCurrencyIndicator, strikeCurrencyIndicator, numberInstrumentCirculating, parValue, quantityNotation, instUnitExp, settlementDelay, strikeCurrency, taxCode, typeOfCorporateEvent, typeOfMarketAdmission, repoIndicator, issuePrice, nominalCurrency, issuePriceDecimals, strikePriceDecimals, liquidInstrumentIndicator, marketOfReferenceMic, icbCode, thresholdLisPostTrade60mn, thresholdLisPostTrade120mn, thresholdLisPostTradeEod, longMnemonic, maxOrderAmountCall, maxOrderAmountContinuous, maxOrderQuantityCall, maxOrderQuantityContinuous, poolFactor, emmPatternRepGroups }, bytes)

theorem encode_length_pos (message : StandingDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StandingDataMessage) : (encode message).length ≤ 4533 := by
  have bound_emmPatternRepGroups := EmmPatternRepGroups.encode_length_le message.emmPatternRepGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, TypeOfMarketAdmission.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : StandingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfMarketAdmission.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [EmmPatternRepGroups.decode_encode, some_bind]
  rfl

end StandingDataMessage

/-- Real Time Index Message: 50 bytes -/
structure RealTimeIndexMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  symbolIndex : BitVec 32
  indexLevel : BitVec 64
  pctgOfCapitalization : BitVec 64
  prctVarfromPrevClose : BitVec 64
  numTradedInstruments : BitVec 16
  indexLevelType : BitVec 8
  indexPriceCode : BitVec 8
  deriving DecidableEq, Repr

namespace RealTimeIndexMessage

def encode (message : RealTimeIndexMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.indexLevel
    ++ (encodeUIntLE 8 message.pctgOfCapitalization
    ++ (encodeUIntLE 8 message.prctVarfromPrevClose
    ++ (encodeUIntLE 2 message.numTradedInstruments
    ++ (encodeUInt 1 message.indexLevelType
    ++ (encodeUInt 1 message.indexPriceCode))))))))))

def decode (bytes : List UInt8) : Option (RealTimeIndexMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (indexLevel, bytes) ← decodeUIntLE 8 bytes
  let (pctgOfCapitalization, bytes) ← decodeUIntLE 8 bytes
  let (prctVarfromPrevClose, bytes) ← decodeUIntLE 8 bytes
  let (numTradedInstruments, bytes) ← decodeUIntLE 2 bytes
  let (indexLevelType, bytes) ← decodeUInt 1 bytes
  let (indexPriceCode, bytes) ← decodeUInt 1 bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, symbolIndex, indexLevel, pctgOfCapitalization, prctVarfromPrevClose, numTradedInstruments, indexLevelType, indexPriceCode }, bytes)

@[simp] theorem encode_length (message : RealTimeIndexMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RealTimeIndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RealTimeIndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RealTimeIndexMessage

/-- New Stats Group: 9 bytes -/
structure NewStatsGroup where
  statsUpdateType : BitVec 8
  statsUpdateValue : BitVec 64
  deriving DecidableEq, Repr

namespace NewStatsGroup

def encode (message : NewStatsGroup) : List UInt8 :=
  encodeUInt 1 message.statsUpdateType
    ++ (encodeUIntLE 8 message.statsUpdateValue)

def decode (bytes : List UInt8) : Option (NewStatsGroup × List UInt8) := do
  let (statsUpdateType, bytes) ← decodeUInt 1 bytes
  let (statsUpdateValue, bytes) ← decodeUIntLE 8 bytes
  pure ({ statsUpdateType, statsUpdateValue }, bytes)

@[simp] theorem encode_length (message : NewStatsGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : NewStatsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewStatsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewStatsGroup

/-- New Stats Groups -/
structure NewStatsGroups where
  blockLengthShort : BitVec 8
  newStatsGroup : Bounded 1 NewStatsGroup
  deriving DecidableEq, Repr

namespace NewStatsGroups

def encode (message : NewStatsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.newStatsGroup.val.length)
    ++ (encodeMany NewStatsGroup.encode message.newStatsGroup.val))

def decode (bytes : List UInt8) : Option (NewStatsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (newStatsGroup_, bytes) ← decodeMany NewStatsGroup.decode numInGroup.toNat bytes
  if fits_newStatsGroup : newStatsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, newStatsGroup := ⟨newStatsGroup_, fits_newStatsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewStatsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewStatsGroups) : (encode message).length ≤ 2297 := by
  have bound_newStatsGroup := message.newStatsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const NewStatsGroup.encode 9 NewStatsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : NewStatsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 NewStatsGroup.encode NewStatsGroup.decode NewStatsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newStatsGroup.length_lt]
  rfl

end NewStatsGroups

/-- Statistics Message -/
structure StatisticsMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  newStatsGroups : NewStatsGroups
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (NewStatsGroups.encode message.newStatsGroups)))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (newStatsGroups, bytes) ← NewStatsGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, symbolIndex, newStatsGroups }, bytes)

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StatisticsMessage) : (encode message).length ≤ 2310 := by
  have bound_newStatsGroups := NewStatsGroups.encode_length_le message.newStatsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [NewStatsGroups.decode_encode, some_bind]
  rfl

end StatisticsMessage

/-- Index Summary Message: 126 bytes -/
structure IndexSummaryMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  symbolIndex : BitVec 32
  openingLevel : BitVec 64
  openingTime : BitVec 64
  confirmedReferenceLevel : BitVec 64
  confirmedReferenceTime : BitVec 64
  closingReferenceLevel : BitVec 64
  closingReferenceTime : BitVec 64
  prctVarfromPrevClose : BitVec 64
  highLevel : BitVec 64
  highTime : BitVec 64
  lowLevel : BitVec 64
  lowTime : BitVec 64
  liquidationLevel : BitVec 64
  liquidationTime : BitVec 64
  deriving DecidableEq, Repr

namespace IndexSummaryMessage

def encode (message : IndexSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.openingLevel
    ++ (encodeUIntLE 8 message.openingTime
    ++ (encodeUIntLE 8 message.confirmedReferenceLevel
    ++ (encodeUIntLE 8 message.confirmedReferenceTime
    ++ (encodeUIntLE 8 message.closingReferenceLevel
    ++ (encodeUIntLE 8 message.closingReferenceTime
    ++ (encodeUIntLE 8 message.prctVarfromPrevClose
    ++ (encodeUIntLE 8 message.highLevel
    ++ (encodeUIntLE 8 message.highTime
    ++ (encodeUIntLE 8 message.lowLevel
    ++ (encodeUIntLE 8 message.lowTime
    ++ (encodeUIntLE 8 message.liquidationLevel
    ++ (encodeUIntLE 8 message.liquidationTime)))))))))))))))))

def decode (bytes : List UInt8) : Option (IndexSummaryMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (openingLevel, bytes) ← decodeUIntLE 8 bytes
  let (openingTime, bytes) ← decodeUIntLE 8 bytes
  let (confirmedReferenceLevel, bytes) ← decodeUIntLE 8 bytes
  let (confirmedReferenceTime, bytes) ← decodeUIntLE 8 bytes
  let (closingReferenceLevel, bytes) ← decodeUIntLE 8 bytes
  let (closingReferenceTime, bytes) ← decodeUIntLE 8 bytes
  let (prctVarfromPrevClose, bytes) ← decodeUIntLE 8 bytes
  let (highLevel, bytes) ← decodeUIntLE 8 bytes
  let (highTime, bytes) ← decodeUIntLE 8 bytes
  let (lowLevel, bytes) ← decodeUIntLE 8 bytes
  let (lowTime, bytes) ← decodeUIntLE 8 bytes
  let (liquidationLevel, bytes) ← decodeUIntLE 8 bytes
  let (liquidationTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, symbolIndex, openingLevel, openingTime, confirmedReferenceLevel, confirmedReferenceTime, closingReferenceLevel, closingReferenceTime, prctVarfromPrevClose, highLevel, highTime, lowLevel, lowTime, liquidationLevel, liquidationTime }, bytes)

@[simp] theorem encode_length (message : IndexSummaryMessage) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : IndexSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexSummaryMessage

/-- Strategy Standing Data Group: 17 bytes -/
structure StrategyStandingDataGroup where
  legSymbolIndex : BitVec 32
  legPrice : BitVec 64
  legRatio : BitVec 32
  legBuySell : LegBuySell
  deriving DecidableEq, Repr

namespace StrategyStandingDataGroup

def encode (message : StrategyStandingDataGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSymbolIndex
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legRatio
    ++ (LegBuySell.encode message.legBuySell)))

def decode (bytes : List UInt8) : Option (StrategyStandingDataGroup × List UInt8) := do
  let (legSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  let (legBuySell, bytes) ← LegBuySell.decode bytes
  pure ({ legSymbolIndex, legPrice, legRatio, legBuySell }, bytes)

@[simp] theorem encode_length (message : StrategyStandingDataGroup) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegBuySell.encode_length]

theorem encode_length_pos (message : StrategyStandingDataGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyStandingDataGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LegBuySell.decode_encode, some_bind]
  rfl

end StrategyStandingDataGroup

/-- Strategy Standing Data Groups -/
structure StrategyStandingDataGroups where
  blockLengthShort : BitVec 8
  strategyStandingDataGroup : Bounded 1 StrategyStandingDataGroup
  deriving DecidableEq, Repr

namespace StrategyStandingDataGroups

def encode (message : StrategyStandingDataGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.strategyStandingDataGroup.val.length)
    ++ (encodeMany StrategyStandingDataGroup.encode message.strategyStandingDataGroup.val))

def decode (bytes : List UInt8) : Option (StrategyStandingDataGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (strategyStandingDataGroup_, bytes) ← decodeMany StrategyStandingDataGroup.decode numInGroup.toNat bytes
  if fits_strategyStandingDataGroup : strategyStandingDataGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, strategyStandingDataGroup := ⟨strategyStandingDataGroup_, fits_strategyStandingDataGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyStandingDataGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyStandingDataGroups) : (encode message).length ≤ 4337 := by
  have bound_strategyStandingDataGroup := message.strategyStandingDataGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const StrategyStandingDataGroup.encode 17 StrategyStandingDataGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyStandingDataGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 StrategyStandingDataGroup.encode StrategyStandingDataGroup.decode StrategyStandingDataGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyStandingDataGroup.length_lt]
  rfl

end StrategyStandingDataGroups

/-- Strategy Standing Data Message -/
structure StrategyStandingDataMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  symbolIndex : BitVec 32
  derivativesInstrumentTradingCode : Alpha 18
  exchangeCode : ExchangeCode
  maturityDate : Alpha 8
  strategyCode : StrategyCode
  contractSymbolIndex : BitVec 32
  cfiOptional : Alpha 6
  strategyStandingDataGroups : StrategyStandingDataGroups
  deriving DecidableEq, Repr

namespace StrategyStandingDataMessage

def encode (message : StrategyStandingDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.derivativesInstrumentTradingCode
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (Alpha.encode message.maturityDate
    ++ (StrategyCode.encode message.strategyCode
    ++ (encodeUIntLE 4 message.contractSymbolIndex
    ++ (Alpha.encode message.cfiOptional
    ++ (StrategyStandingDataGroups.encode message.strategyStandingDataGroups))))))))))

def decode (bytes : List UInt8) : Option (StrategyStandingDataMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (derivativesInstrumentTradingCode, bytes) ← Alpha.decode 18 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (strategyCode, bytes) ← StrategyCode.decode bytes
  let (contractSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (cfiOptional, bytes) ← Alpha.decode 6 bytes
  let (strategyStandingDataGroups, bytes) ← StrategyStandingDataGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, symbolIndex, derivativesInstrumentTradingCode, exchangeCode, maturityDate, strategyCode, contractSymbolIndex, cfiOptional, strategyStandingDataGroups }, bytes)

theorem encode_length_pos (message : StrategyStandingDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyStandingDataMessage) : (encode message).length ≤ 4389 := by
  have bound_strategyStandingDataGroups := StrategyStandingDataGroups.encode_length_le message.strategyStandingDataGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExchangeCode.encode_length, StrategyCode.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyStandingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrategyStandingDataGroups.decode_encode, some_bind]
  rfl

end StrategyStandingDataMessage

/-- Contract Emm Properties Group: 27 bytes -/
structure ContractEmmPropertiesGroup where
  emmOptional : BitVec 8
  tickSizeIndexId : BitVec 16
  patternId : BitVec 16
  lotSizeOptional : BitVec 64
  strategyAuthorized : BitVec 64
  dynamicCollarLogic : BitVec 8
  collarMaxUnhaltNb : BitVec 8
  collarUnhaltDelay : BitVec 32
  deriving DecidableEq, Repr

namespace ContractEmmPropertiesGroup

def encode (message : ContractEmmPropertiesGroup) : List UInt8 :=
  encodeUInt 1 message.emmOptional
    ++ (encodeUIntLE 2 message.tickSizeIndexId
    ++ (encodeUIntLE 2 message.patternId
    ++ (encodeUIntLE 8 message.lotSizeOptional
    ++ (encodeUIntLE 8 message.strategyAuthorized
    ++ (encodeUInt 1 message.dynamicCollarLogic
    ++ (encodeUInt 1 message.collarMaxUnhaltNb
    ++ (encodeUIntLE 4 message.collarUnhaltDelay)))))))

def decode (bytes : List UInt8) : Option (ContractEmmPropertiesGroup × List UInt8) := do
  let (emmOptional, bytes) ← decodeUInt 1 bytes
  let (tickSizeIndexId, bytes) ← decodeUIntLE 2 bytes
  let (patternId, bytes) ← decodeUIntLE 2 bytes
  let (lotSizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (strategyAuthorized, bytes) ← decodeUIntLE 8 bytes
  let (dynamicCollarLogic, bytes) ← decodeUInt 1 bytes
  let (collarMaxUnhaltNb, bytes) ← decodeUInt 1 bytes
  let (collarUnhaltDelay, bytes) ← decodeUIntLE 4 bytes
  pure ({ emmOptional, tickSizeIndexId, patternId, lotSizeOptional, strategyAuthorized, dynamicCollarLogic, collarMaxUnhaltNb, collarUnhaltDelay }, bytes)

@[simp] theorem encode_length (message : ContractEmmPropertiesGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : ContractEmmPropertiesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractEmmPropertiesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ContractEmmPropertiesGroup

/-- Contract Emm Properties Groups -/
structure ContractEmmPropertiesGroups where
  blockLengthShort : BitVec 8
  contractEmmPropertiesGroup : Bounded 1 ContractEmmPropertiesGroup
  deriving DecidableEq, Repr

namespace ContractEmmPropertiesGroups

def encode (message : ContractEmmPropertiesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.contractEmmPropertiesGroup.val.length)
    ++ (encodeMany ContractEmmPropertiesGroup.encode message.contractEmmPropertiesGroup.val))

def decode (bytes : List UInt8) : Option (ContractEmmPropertiesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (contractEmmPropertiesGroup_, bytes) ← decodeMany ContractEmmPropertiesGroup.decode numInGroup.toNat bytes
  if fits_contractEmmPropertiesGroup : contractEmmPropertiesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, contractEmmPropertiesGroup := ⟨contractEmmPropertiesGroup_, fits_contractEmmPropertiesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ContractEmmPropertiesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ContractEmmPropertiesGroups) : (encode message).length ≤ 6887 := by
  have bound_contractEmmPropertiesGroup := message.contractEmmPropertiesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const ContractEmmPropertiesGroup.encode 27 ContractEmmPropertiesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ContractEmmPropertiesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ContractEmmPropertiesGroup.encode ContractEmmPropertiesGroup.decode ContractEmmPropertiesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.contractEmmPropertiesGroup.length_lt]
  rfl

end ContractEmmPropertiesGroups

/-- Contract Standing Data Message -/
structure ContractStandingDataMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  optiqSegment : BitVec 8
  partitionId : BitVec 16
  contractEventDate : BitVec 16
  exchangeCode : ExchangeCode
  exerStyle : BitVec 8
  contractName : Alpha 60
  contractType : ContractType
  underlyingType : UnderlyingType
  priceDecimalsOptional : BitVec 8
  quantityDecimals : BitVec 8
  amountDecimals : BitVec 8
  ratioDecimalsOptional : BitVec 8
  mainDepositary : Alpha 5
  mic : Alpha 4
  countryOfExchange : Alpha 3
  productCode : Alpha 4
  underlyingMic : Alpha 4
  underlyingIsinCode : Alpha 12
  underlyingExpiry : BitVec 32
  orderTypeRules : BitVec 16
  settlementMethod : Alpha 1
  tradingCurrency : Alpha 3
  strikePriceDecimalsRatio : BitVec 8
  mmProtections : BitVec 8
  contractTradingType : BitVec 8
  instUnitExp : BitVec 8
  underlyingSubtype : BitVec 8
  motherStockIsin : Alpha 12
  settlementTickSize : BitVec 64
  edspTickSize : BitVec 64
  underlyingSymbolIndex : BitVec 32
  tradingPolicy : BitVec 8
  referenceSpreadTableId : BitVec 16
  derivativesMarketModel : BitVec 8
  tradingUnit : BitVec 64
  referencePriceOriginInOpeningCall : BitVec 8
  referencePriceOriginInContinuous : BitVec 8
  referencePriceOriginInTradingInterruption : BitVec 8
  collarExpansionFactor : BitVec 8
  mifidiiLiquidFlag : BitVec 8
  pricingAlgorithm : BitVec 8
  contractEmmPropertiesGroups : ContractEmmPropertiesGroups
  deriving DecidableEq, Repr

namespace ContractStandingDataMessage

def encode (message : ContractStandingDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.optiqSegment
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUIntLE 2 message.contractEventDate
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUInt 1 message.exerStyle
    ++ (Alpha.encode message.contractName
    ++ (ContractType.encode message.contractType
    ++ (UnderlyingType.encode message.underlyingType
    ++ (encodeUInt 1 message.priceDecimalsOptional
    ++ (encodeUInt 1 message.quantityDecimals
    ++ (encodeUInt 1 message.amountDecimals
    ++ (encodeUInt 1 message.ratioDecimalsOptional
    ++ (Alpha.encode message.mainDepositary
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.countryOfExchange
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.underlyingMic
    ++ (Alpha.encode message.underlyingIsinCode
    ++ (encodeUIntLE 4 message.underlyingExpiry
    ++ (encodeUIntLE 2 message.orderTypeRules
    ++ (Alpha.encode message.settlementMethod
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 1 message.strikePriceDecimalsRatio
    ++ (encodeUIntLE 1 message.mmProtections
    ++ (encodeUInt 1 message.contractTradingType
    ++ (encodeUInt 1 message.instUnitExp
    ++ (encodeUInt 1 message.underlyingSubtype
    ++ (Alpha.encode message.motherStockIsin
    ++ (encodeUIntLE 8 message.settlementTickSize
    ++ (encodeUIntLE 8 message.edspTickSize
    ++ (encodeUIntLE 4 message.underlyingSymbolIndex
    ++ (encodeUInt 1 message.tradingPolicy
    ++ (encodeUIntLE 2 message.referenceSpreadTableId
    ++ (encodeUInt 1 message.derivativesMarketModel
    ++ (encodeUIntLE 8 message.tradingUnit
    ++ (encodeUInt 1 message.referencePriceOriginInOpeningCall
    ++ (encodeUInt 1 message.referencePriceOriginInContinuous
    ++ (encodeUInt 1 message.referencePriceOriginInTradingInterruption
    ++ (encodeUInt 1 message.collarExpansionFactor
    ++ (encodeUInt 1 message.mifidiiLiquidFlag
    ++ (encodeUInt 1 message.pricingAlgorithm
    ++ (ContractEmmPropertiesGroups.encode message.contractEmmPropertiesGroups))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ContractStandingDataMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (optiqSegment, bytes) ← decodeUInt 1 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (contractEventDate, bytes) ← decodeUIntLE 2 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (exerStyle, bytes) ← decodeUInt 1 bytes
  let (contractName, bytes) ← Alpha.decode 60 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (priceDecimalsOptional, bytes) ← decodeUInt 1 bytes
  let (quantityDecimals, bytes) ← decodeUInt 1 bytes
  let (amountDecimals, bytes) ← decodeUInt 1 bytes
  let (ratioDecimalsOptional, bytes) ← decodeUInt 1 bytes
  let (mainDepositary, bytes) ← Alpha.decode 5 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (countryOfExchange, bytes) ← Alpha.decode 3 bytes
  let (productCode, bytes) ← Alpha.decode 4 bytes
  let (underlyingMic, bytes) ← Alpha.decode 4 bytes
  let (underlyingIsinCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingExpiry, bytes) ← decodeUIntLE 4 bytes
  let (orderTypeRules, bytes) ← decodeUIntLE 2 bytes
  let (settlementMethod, bytes) ← Alpha.decode 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (strikePriceDecimalsRatio, bytes) ← decodeUInt 1 bytes
  let (mmProtections, bytes) ← decodeUIntLE 1 bytes
  let (contractTradingType, bytes) ← decodeUInt 1 bytes
  let (instUnitExp, bytes) ← decodeUInt 1 bytes
  let (underlyingSubtype, bytes) ← decodeUInt 1 bytes
  let (motherStockIsin, bytes) ← Alpha.decode 12 bytes
  let (settlementTickSize, bytes) ← decodeUIntLE 8 bytes
  let (edspTickSize, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (tradingPolicy, bytes) ← decodeUInt 1 bytes
  let (referenceSpreadTableId, bytes) ← decodeUIntLE 2 bytes
  let (derivativesMarketModel, bytes) ← decodeUInt 1 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 8 bytes
  let (referencePriceOriginInOpeningCall, bytes) ← decodeUInt 1 bytes
  let (referencePriceOriginInContinuous, bytes) ← decodeUInt 1 bytes
  let (referencePriceOriginInTradingInterruption, bytes) ← decodeUInt 1 bytes
  let (collarExpansionFactor, bytes) ← decodeUInt 1 bytes
  let (mifidiiLiquidFlag, bytes) ← decodeUInt 1 bytes
  let (pricingAlgorithm, bytes) ← decodeUInt 1 bytes
  let (contractEmmPropertiesGroups, bytes) ← ContractEmmPropertiesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, symbolIndex, optiqSegment, partitionId, contractEventDate, exchangeCode, exerStyle, contractName, contractType, underlyingType, priceDecimalsOptional, quantityDecimals, amountDecimals, ratioDecimalsOptional, mainDepositary, mic, countryOfExchange, productCode, underlyingMic, underlyingIsinCode, underlyingExpiry, orderTypeRules, settlementMethod, tradingCurrency, strikePriceDecimalsRatio, mmProtections, contractTradingType, instUnitExp, underlyingSubtype, motherStockIsin, settlementTickSize, edspTickSize, underlyingSymbolIndex, tradingPolicy, referenceSpreadTableId, derivativesMarketModel, tradingUnit, referencePriceOriginInOpeningCall, referencePriceOriginInContinuous, referencePriceOriginInTradingInterruption, collarExpansionFactor, mifidiiLiquidFlag, pricingAlgorithm, contractEmmPropertiesGroups }, bytes)

theorem encode_length_pos (message : ContractStandingDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ContractStandingDataMessage) : (encode message).length ≤ 7070 := by
  have bound_contractEmmPropertiesGroups := ContractEmmPropertiesGroups.encode_length_le message.contractEmmPropertiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExchangeCode.encode_length, Alpha.encode_length, ContractType.encode_length, UnderlyingType.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ContractStandingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [ContractEmmPropertiesGroups.decode_encode, some_bind]
  rfl

end ContractStandingDataMessage

/-- Outright Rep Group: 1 bytes -/
structure OutrightRepGroup where
  emm : BitVec 8
  deriving DecidableEq, Repr

namespace OutrightRepGroup

def encode (message : OutrightRepGroup) : List UInt8 :=
  encodeUInt 1 message.emm

def decode (bytes : List UInt8) : Option (OutrightRepGroup × List UInt8) := do
  let (emm, bytes) ← decodeUInt 1 bytes
  pure ({ emm }, bytes)

@[simp] theorem encode_length (message : OutrightRepGroup) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : OutrightRepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightRepGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OutrightRepGroup

/-- Outright Rep Groups -/
structure OutrightRepGroups where
  blockLengthShort : BitVec 8
  outrightRepGroup : Bounded 1 OutrightRepGroup
  deriving DecidableEq, Repr

namespace OutrightRepGroups

def encode (message : OutrightRepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.outrightRepGroup.val.length)
    ++ (encodeMany OutrightRepGroup.encode message.outrightRepGroup.val))

def decode (bytes : List UInt8) : Option (OutrightRepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (outrightRepGroup_, bytes) ← decodeMany OutrightRepGroup.decode numInGroup.toNat bytes
  if fits_outrightRepGroup : outrightRepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, outrightRepGroup := ⟨outrightRepGroup_, fits_outrightRepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OutrightRepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OutrightRepGroups) : (encode message).length ≤ 257 := by
  have bound_outrightRepGroup := message.outrightRepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const OutrightRepGroup.encode 1 OutrightRepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OutrightRepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OutrightRepGroup.encode OutrightRepGroup.decode OutrightRepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.outrightRepGroup.length_lt]
  rfl

end OutrightRepGroups

/-- Outright Standing Data Message -/
structure OutrightStandingDataMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  contractSymbolIndex : BitVec 32
  instrumentEventDate : BitVec 16
  isinCode : Alpha 12
  cfiOptional : Alpha 6
  maturityDate : Alpha 8
  lotSize : BitVec 64
  strikePrice : BitVec 64
  lastTradingDate : BitVec 16
  daysToExpiry : BitVec 16
  derivativesInstrumentTradingCodeOptional : Alpha 18
  derivativesInstrumentType : BitVec 8
  expiryCycleType : BitVec 8
  underlyingDerivativesInstrumentTradingCode : Alpha 18
  underlyingSymbolIndex : BitVec 32
  tradingUnit : BitVec 64
  outrightRepGroups : OutrightRepGroups
  deriving DecidableEq, Repr

namespace OutrightStandingDataMessage

def encode (message : OutrightStandingDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.contractSymbolIndex
    ++ (encodeUIntLE 2 message.instrumentEventDate
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.cfiOptional
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 8 message.lotSize
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 2 message.lastTradingDate
    ++ (encodeUIntLE 2 message.daysToExpiry
    ++ (Alpha.encode message.derivativesInstrumentTradingCodeOptional
    ++ (encodeUInt 1 message.derivativesInstrumentType
    ++ (encodeUInt 1 message.expiryCycleType
    ++ (Alpha.encode message.underlyingDerivativesInstrumentTradingCode
    ++ (encodeUIntLE 4 message.underlyingSymbolIndex
    ++ (encodeUIntLE 8 message.tradingUnit
    ++ (OutrightRepGroups.encode message.outrightRepGroups))))))))))))))))))

def decode (bytes : List UInt8) : Option (OutrightStandingDataMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (contractSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (instrumentEventDate, bytes) ← decodeUIntLE 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (cfiOptional, bytes) ← Alpha.decode 6 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 2 bytes
  let (daysToExpiry, bytes) ← decodeUIntLE 2 bytes
  let (derivativesInstrumentTradingCodeOptional, bytes) ← Alpha.decode 18 bytes
  let (derivativesInstrumentType, bytes) ← decodeUInt 1 bytes
  let (expiryCycleType, bytes) ← decodeUInt 1 bytes
  let (underlyingDerivativesInstrumentTradingCode, bytes) ← Alpha.decode 18 bytes
  let (underlyingSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 8 bytes
  let (outrightRepGroups, bytes) ← OutrightRepGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, symbolIndex, contractSymbolIndex, instrumentEventDate, isinCode, cfiOptional, maturityDate, lotSize, strikePrice, lastTradingDate, daysToExpiry, derivativesInstrumentTradingCodeOptional, derivativesInstrumentType, expiryCycleType, underlyingDerivativesInstrumentTradingCode, underlyingSymbolIndex, tradingUnit, outrightRepGroups }, bytes)

theorem encode_length_pos (message : OutrightStandingDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OutrightStandingDataMessage) : (encode message).length ≤ 372 := by
  have bound_outrightRepGroups := OutrightRepGroups.encode_length_le message.outrightRepGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : OutrightStandingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OutrightRepGroups.decode_encode, some_bind]
  rfl

end OutrightStandingDataMessage

/-- Long Order Updates Group: 49 bytes -/
structure LongOrderUpdatesGroup where
  symbolIndex : BitVec 32
  actionType : BitVec 8
  orderPriority : BitVec 64
  previousPriority : BitVec 64
  orderType : BitVec 8
  orderPx : BitVec 64
  orderSide : BitVec 8
  orderQuantity : BitVec 64
  pegOffset : BitVec 8
  firmId : Alpha 8
  accountType : BitVec 8
  deriving DecidableEq, Repr

namespace LongOrderUpdatesGroup

def encode (message : LongOrderUpdatesGroup) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.actionType
    ++ (encodeUIntLE 8 message.orderPriority
    ++ (encodeUIntLE 8 message.previousPriority
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUIntLE 8 message.orderPx
    ++ (encodeUInt 1 message.orderSide
    ++ (encodeUIntLE 8 message.orderQuantity
    ++ (encodeUInt 1 message.pegOffset
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 1 message.accountType))))))))))

def decode (bytes : List UInt8) : Option (LongOrderUpdatesGroup × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (actionType, bytes) ← decodeUInt 1 bytes
  let (orderPriority, bytes) ← decodeUIntLE 8 bytes
  let (previousPriority, bytes) ← decodeUIntLE 8 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (orderPx, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (orderQuantity, bytes) ← decodeUIntLE 8 bytes
  let (pegOffset, bytes) ← decodeUInt 1 bytes
  let (firmId, bytes) ← Alpha.decode 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, actionType, orderPriority, previousPriority, orderType, orderPx, orderSide, orderQuantity, pegOffset, firmId, accountType }, bytes)

@[simp] theorem encode_length (message : LongOrderUpdatesGroup) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LongOrderUpdatesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongOrderUpdatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongOrderUpdatesGroup

/-- Long Order Updates Groups -/
structure LongOrderUpdatesGroups where
  blockLengthShort : BitVec 8
  longOrderUpdatesGroup : Bounded 1 LongOrderUpdatesGroup
  deriving DecidableEq, Repr

namespace LongOrderUpdatesGroups

def encode (message : LongOrderUpdatesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.longOrderUpdatesGroup.val.length)
    ++ (encodeMany LongOrderUpdatesGroup.encode message.longOrderUpdatesGroup.val))

def decode (bytes : List UInt8) : Option (LongOrderUpdatesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (longOrderUpdatesGroup_, bytes) ← decodeMany LongOrderUpdatesGroup.decode numInGroup.toNat bytes
  if fits_longOrderUpdatesGroup : longOrderUpdatesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, longOrderUpdatesGroup := ⟨longOrderUpdatesGroup_, fits_longOrderUpdatesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongOrderUpdatesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderUpdatesGroups) : (encode message).length ≤ 12497 := by
  have bound_longOrderUpdatesGroup := message.longOrderUpdatesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LongOrderUpdatesGroup.encode 49 LongOrderUpdatesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOrderUpdatesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LongOrderUpdatesGroup.encode LongOrderUpdatesGroup.decode LongOrderUpdatesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longOrderUpdatesGroup.length_lt]
  rfl

end LongOrderUpdatesGroups

/-- Long Order Update Message -/
structure LongOrderUpdateMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  longOrderUpdatesGroups : LongOrderUpdatesGroups
  deriving DecidableEq, Repr

namespace LongOrderUpdateMessage

def encode (message : LongOrderUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (LongOrderUpdatesGroups.encode message.longOrderUpdatesGroups))))

def decode (bytes : List UInt8) : Option (LongOrderUpdateMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (longOrderUpdatesGroups, bytes) ← LongOrderUpdatesGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, longOrderUpdatesGroups }, bytes)

theorem encode_length_pos (message : LongOrderUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOrderUpdateMessage) : (encode message).length ≤ 12515 := by
  have bound_longOrderUpdatesGroups := LongOrderUpdatesGroups.encode_length_le message.longOrderUpdatesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : LongOrderUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LongOrderUpdatesGroups.decode_encode, some_bind]
  rfl

end LongOrderUpdateMessage

/-- Package Components Group: 24 bytes -/
structure PackageComponentsGroup where
  legSymbolIndex : BitVec 32
  legRatio : BitVec 32
  legLastPx : BitVec 64
  legLastQty : BitVec 64
  deriving DecidableEq, Repr

namespace PackageComponentsGroup

def encode (message : PackageComponentsGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSymbolIndex
    ++ (encodeUIntLE 4 message.legRatio
    ++ (encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 8 message.legLastQty)))

def decode (bytes : List UInt8) : Option (PackageComponentsGroup × List UInt8) := do
  let (legSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 8 bytes
  pure ({ legSymbolIndex, legRatio, legLastPx, legLastQty }, bytes)

@[simp] theorem encode_length (message : PackageComponentsGroup) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : PackageComponentsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PackageComponentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PackageComponentsGroup

/-- Package Components Groups -/
structure PackageComponentsGroups where
  blockLengthShort : BitVec 8
  packageComponentsGroup : Bounded 1 PackageComponentsGroup
  deriving DecidableEq, Repr

namespace PackageComponentsGroups

def encode (message : PackageComponentsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.packageComponentsGroup.val.length)
    ++ (encodeMany PackageComponentsGroup.encode message.packageComponentsGroup.val))

def decode (bytes : List UInt8) : Option (PackageComponentsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (packageComponentsGroup_, bytes) ← decodeMany PackageComponentsGroup.decode numInGroup.toNat bytes
  if fits_packageComponentsGroup : packageComponentsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, packageComponentsGroup := ⟨packageComponentsGroup_, fits_packageComponentsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PackageComponentsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PackageComponentsGroups) : (encode message).length ≤ 6122 := by
  have bound_packageComponentsGroup := message.packageComponentsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const PackageComponentsGroup.encode 24 PackageComponentsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PackageComponentsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PackageComponentsGroup.encode PackageComponentsGroup.decode PackageComponentsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.packageComponentsGroup.length_lt]
  rfl

end PackageComponentsGroups

/-- Lis Package Structure Message -/
structure LisPackageStructureMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  contractSymbolIndex : BitVec 32
  mifidExecutionId : Alpha 52
  strategyCode : StrategyCode
  packageComponentsGroups : PackageComponentsGroups
  deriving DecidableEq, Repr

namespace LisPackageStructureMessage

def encode (message : LisPackageStructureMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 4 message.contractSymbolIndex
    ++ (Alpha.encode message.mifidExecutionId
    ++ (StrategyCode.encode message.strategyCode
    ++ (PackageComponentsGroups.encode message.packageComponentsGroups)))))))

def decode (bytes : List UInt8) : Option (LisPackageStructureMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (contractSymbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (mifidExecutionId, bytes) ← Alpha.decode 52 bytes
  let (strategyCode, bytes) ← StrategyCode.decode bytes
  let (packageComponentsGroups, bytes) ← PackageComponentsGroups.decode bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, contractSymbolIndex, mifidExecutionId, strategyCode, packageComponentsGroups }, bytes)

theorem encode_length_pos (message : LisPackageStructureMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LisPackageStructureMessage) : (encode message).length ≤ 6197 := by
  have bound_packageComponentsGroups := PackageComponentsGroups.encode_length_le message.packageComponentsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, StrategyCode.encode_length]
  omega

@[simp] theorem decode_encode (message : LisPackageStructureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyCode.decode_encode, some_bind]
  dsimp only
  rw [PackageComponentsGroups.decode_encode, some_bind]
  rfl

end LisPackageStructureMessage

/-- Apa Quotes Message: 105 bytes -/
structure ApaQuotesMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  mifidInstrumentIdType : Alpha 4
  mifidInstrumentId : Alpha 12
  mic : Alpha 4
  currency : Alpha 3
  leiCode : Alpha 20
  eventTime : BitVec 64
  quoteUpdateType : BitVec 8
  mifidPrice : Alpha 20
  mifidQuantity : Alpha 20
  apaOrigin : Alpha 4
  deriving DecidableEq, Repr

namespace ApaQuotesMessage

def encode (message : ApaQuotesMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (Alpha.encode message.mifidInstrumentIdType
    ++ (Alpha.encode message.mifidInstrumentId
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.leiCode
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUInt 1 message.quoteUpdateType
    ++ (Alpha.encode message.mifidPrice
    ++ (Alpha.encode message.mifidQuantity
    ++ (Alpha.encode message.apaOrigin)))))))))))

def decode (bytes : List UInt8) : Option (ApaQuotesMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (mifidInstrumentIdType, bytes) ← Alpha.decode 4 bytes
  let (mifidInstrumentId, bytes) ← Alpha.decode 12 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (leiCode, bytes) ← Alpha.decode 20 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteUpdateType, bytes) ← decodeUInt 1 bytes
  let (mifidPrice, bytes) ← Alpha.decode 20 bytes
  let (mifidQuantity, bytes) ← Alpha.decode 20 bytes
  let (apaOrigin, bytes) ← Alpha.decode 4 bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, mifidInstrumentIdType, mifidInstrumentId, mic, currency, leiCode, eventTime, quoteUpdateType, mifidPrice, mifidQuantity, apaOrigin }, bytes)

@[simp] theorem encode_length (message : ApaQuotesMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ApaQuotesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApaQuotesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApaQuotesMessage

/-- Apa Standing Data Message: 217 bytes -/
structure ApaStandingDataMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  mifidInstrumentIdType : Alpha 4
  mifidInstrumentId : Alpha 12
  fullInstrumentName : Alpha 102
  cfiOptional : Alpha 6
  notionalCurrency : Alpha 3
  secondNotionalCurrency : Alpha 3
  priceMultiplier : BitVec 32
  priceMultiplierDecimals : BitVec 8
  underlyingIsinCode : Alpha 12
  underlyingIndexName : Alpha 25
  underlyingIndexTerm : Alpha 8
  optionType : BitVec 8
  strikePrice : BitVec 64
  strikePriceDecimals : BitVec 8
  exerStyle : BitVec 8
  maturityDateOptional : Alpha 8
  expiryDate : Alpha 8
  settlementMethod : Alpha 1
  deriving DecidableEq, Repr

namespace ApaStandingDataMessage

def encode (message : ApaStandingDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (Alpha.encode message.mifidInstrumentIdType
    ++ (Alpha.encode message.mifidInstrumentId
    ++ (Alpha.encode message.fullInstrumentName
    ++ (Alpha.encode message.cfiOptional
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.secondNotionalCurrency
    ++ (encodeUIntLE 4 message.priceMultiplier
    ++ (encodeUInt 1 message.priceMultiplierDecimals
    ++ (Alpha.encode message.underlyingIsinCode
    ++ (Alpha.encode message.underlyingIndexName
    ++ (Alpha.encode message.underlyingIndexTerm
    ++ (encodeUInt 1 message.optionType
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUInt 1 message.strikePriceDecimals
    ++ (encodeUInt 1 message.exerStyle
    ++ (Alpha.encode message.maturityDateOptional
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.settlementMethod)))))))))))))))))))

def decode (bytes : List UInt8) : Option (ApaStandingDataMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (mifidInstrumentIdType, bytes) ← Alpha.decode 4 bytes
  let (mifidInstrumentId, bytes) ← Alpha.decode 12 bytes
  let (fullInstrumentName, bytes) ← Alpha.decode 102 bytes
  let (cfiOptional, bytes) ← Alpha.decode 6 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (secondNotionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (priceMultiplierDecimals, bytes) ← decodeUInt 1 bytes
  let (underlyingIsinCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingIndexName, bytes) ← Alpha.decode 25 bytes
  let (underlyingIndexTerm, bytes) ← Alpha.decode 8 bytes
  let (optionType, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikePriceDecimals, bytes) ← decodeUInt 1 bytes
  let (exerStyle, bytes) ← decodeUInt 1 bytes
  let (maturityDateOptional, bytes) ← Alpha.decode 8 bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (settlementMethod, bytes) ← Alpha.decode 1 bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, mifidInstrumentIdType, mifidInstrumentId, fullInstrumentName, cfiOptional, notionalCurrency, secondNotionalCurrency, priceMultiplier, priceMultiplierDecimals, underlyingIsinCode, underlyingIndexName, underlyingIndexTerm, optionType, strikePrice, strikePriceDecimals, exerStyle, maturityDateOptional, expiryDate, settlementMethod }, bytes)

@[simp] theorem encode_length (message : ApaStandingDataMessage) : (encode message).length = 217 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ApaStandingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApaStandingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApaStandingDataMessage

/-- Apa Full Trade Information Message: 405 bytes -/
structure ApaFullTradeInformationMessage where
  mdSeqNum : BitVec 64
  rebroadcastIndicator : BitVec 8
  emm : BitVec 8
  eventTime : BitVec 64
  tradingDateTime : Alpha 27
  publicationDateTime : Alpha 27
  tradeType : BitVec 8
  mifidInstrumentIdTypeOptional : Alpha 4
  mifidInstrumentIdOptional : Alpha 12
  mifidTransactionId : Alpha 52
  mifidPriceOptional : Alpha 20
  mifidQuantity : Alpha 20
  mifidPriceNotation : Alpha 4
  mifidCurrency : Alpha 3
  mifidQtyInMsrmtUnitNotation : Alpha 25
  mifidQuantityMeasurementUnit : Alpha 20
  mifidNotionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  mifidClearingFlag : Alpha 5
  efficientMmtMarketMechanism : BitVec 8
  efficientMmtTradingMode : EfficientMmtTradingMode
  efficientMmtTransactionCategory : EfficientMmtTransactionCategory
  efficientMmtNegotiationIndicator : EfficientMmtNegotiationIndicator
  efficientMmtAgencyCrossTradeIndicator : EfficientMmtAgencyCrossTradeIndicator
  efficientMmtModificationIndicator : EfficientMmtModificationIndicator
  efficientMmtBenchmarkIndicator : EfficientMmtBenchmarkIndicator
  efficientMmtSpecialDividendIndicator : EfficientMmtSpecialDividendIndicator
  efficientMmtOffBookAutomatedIndicator : EfficientMmtOffBookAutomatedIndicator
  efficientMmtContributiontoPrice : EfficientMmtContributiontoPrice
  efficientMmtAlgorithmicIndicator : EfficientMmtAlgorithmicIndicator
  efficientMmtPublicationMode : EfficientMmtPublicationMode
  efficientMmtPostTradeDeferral : EfficientMmtPostTradeDeferral
  efficientMmtDuplicativeIndicator : EfficientMmtDuplicativeIndicator
  tradeReference : Alpha 30
  originalReportTimestamp : BitVec 64
  priceMultiplier : BitVec 32
  priceMultiplierDecimals : BitVec 8
  venue : Alpha 11
  mifidEmissionAllowanceType : Alpha 4
  longTradeReference : Alpha 52
  apaOrigin : Alpha 4
  tradeUniqueIdentifier : Alpha 16
  deriving DecidableEq, Repr

namespace ApaFullTradeInformationMessage

def encode (message : ApaFullTradeInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNum
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUInt 1 message.emm
    ++ (encodeUIntLE 8 message.eventTime
    ++ (Alpha.encode message.tradingDateTime
    ++ (Alpha.encode message.publicationDateTime
    ++ (encodeUInt 1 message.tradeType
    ++ (Alpha.encode message.mifidInstrumentIdTypeOptional
    ++ (Alpha.encode message.mifidInstrumentIdOptional
    ++ (Alpha.encode message.mifidTransactionId
    ++ (Alpha.encode message.mifidPriceOptional
    ++ (Alpha.encode message.mifidQuantity
    ++ (Alpha.encode message.mifidPriceNotation
    ++ (Alpha.encode message.mifidCurrency
    ++ (Alpha.encode message.mifidQtyInMsrmtUnitNotation
    ++ (Alpha.encode message.mifidQuantityMeasurementUnit
    ++ (Alpha.encode message.mifidNotionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.mifidClearingFlag
    ++ (encodeUInt 1 message.efficientMmtMarketMechanism
    ++ (EfficientMmtTradingMode.encode message.efficientMmtTradingMode
    ++ (EfficientMmtTransactionCategory.encode message.efficientMmtTransactionCategory
    ++ (EfficientMmtNegotiationIndicator.encode message.efficientMmtNegotiationIndicator
    ++ (EfficientMmtAgencyCrossTradeIndicator.encode message.efficientMmtAgencyCrossTradeIndicator
    ++ (EfficientMmtModificationIndicator.encode message.efficientMmtModificationIndicator
    ++ (EfficientMmtBenchmarkIndicator.encode message.efficientMmtBenchmarkIndicator
    ++ (EfficientMmtSpecialDividendIndicator.encode message.efficientMmtSpecialDividendIndicator
    ++ (EfficientMmtOffBookAutomatedIndicator.encode message.efficientMmtOffBookAutomatedIndicator
    ++ (EfficientMmtContributiontoPrice.encode message.efficientMmtContributiontoPrice
    ++ (EfficientMmtAlgorithmicIndicator.encode message.efficientMmtAlgorithmicIndicator
    ++ (EfficientMmtPublicationMode.encode message.efficientMmtPublicationMode
    ++ (EfficientMmtPostTradeDeferral.encode message.efficientMmtPostTradeDeferral
    ++ (EfficientMmtDuplicativeIndicator.encode message.efficientMmtDuplicativeIndicator
    ++ (Alpha.encode message.tradeReference
    ++ (encodeUIntLE 8 message.originalReportTimestamp
    ++ (encodeUIntLE 4 message.priceMultiplier
    ++ (encodeUInt 1 message.priceMultiplierDecimals
    ++ (Alpha.encode message.venue
    ++ (Alpha.encode message.mifidEmissionAllowanceType
    ++ (Alpha.encode message.longTradeReference
    ++ (Alpha.encode message.apaOrigin
    ++ (Alpha.encode message.tradeUniqueIdentifier)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ApaFullTradeInformationMessage × List UInt8) := do
  let (mdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (emm, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingDateTime, bytes) ← Alpha.decode 27 bytes
  let (publicationDateTime, bytes) ← Alpha.decode 27 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (mifidInstrumentIdTypeOptional, bytes) ← Alpha.decode 4 bytes
  let (mifidInstrumentIdOptional, bytes) ← Alpha.decode 12 bytes
  let (mifidTransactionId, bytes) ← Alpha.decode 52 bytes
  let (mifidPriceOptional, bytes) ← Alpha.decode 20 bytes
  let (mifidQuantity, bytes) ← Alpha.decode 20 bytes
  let (mifidPriceNotation, bytes) ← Alpha.decode 4 bytes
  let (mifidCurrency, bytes) ← Alpha.decode 3 bytes
  let (mifidQtyInMsrmtUnitNotation, bytes) ← Alpha.decode 25 bytes
  let (mifidQuantityMeasurementUnit, bytes) ← Alpha.decode 20 bytes
  let (mifidNotionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (mifidClearingFlag, bytes) ← Alpha.decode 5 bytes
  let (efficientMmtMarketMechanism, bytes) ← decodeUInt 1 bytes
  let (efficientMmtTradingMode, bytes) ← EfficientMmtTradingMode.decode bytes
  let (efficientMmtTransactionCategory, bytes) ← EfficientMmtTransactionCategory.decode bytes
  let (efficientMmtNegotiationIndicator, bytes) ← EfficientMmtNegotiationIndicator.decode bytes
  let (efficientMmtAgencyCrossTradeIndicator, bytes) ← EfficientMmtAgencyCrossTradeIndicator.decode bytes
  let (efficientMmtModificationIndicator, bytes) ← EfficientMmtModificationIndicator.decode bytes
  let (efficientMmtBenchmarkIndicator, bytes) ← EfficientMmtBenchmarkIndicator.decode bytes
  let (efficientMmtSpecialDividendIndicator, bytes) ← EfficientMmtSpecialDividendIndicator.decode bytes
  let (efficientMmtOffBookAutomatedIndicator, bytes) ← EfficientMmtOffBookAutomatedIndicator.decode bytes
  let (efficientMmtContributiontoPrice, bytes) ← EfficientMmtContributiontoPrice.decode bytes
  let (efficientMmtAlgorithmicIndicator, bytes) ← EfficientMmtAlgorithmicIndicator.decode bytes
  let (efficientMmtPublicationMode, bytes) ← EfficientMmtPublicationMode.decode bytes
  let (efficientMmtPostTradeDeferral, bytes) ← EfficientMmtPostTradeDeferral.decode bytes
  let (efficientMmtDuplicativeIndicator, bytes) ← EfficientMmtDuplicativeIndicator.decode bytes
  let (tradeReference, bytes) ← Alpha.decode 30 bytes
  let (originalReportTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (priceMultiplierDecimals, bytes) ← decodeUInt 1 bytes
  let (venue, bytes) ← Alpha.decode 11 bytes
  let (mifidEmissionAllowanceType, bytes) ← Alpha.decode 4 bytes
  let (longTradeReference, bytes) ← Alpha.decode 52 bytes
  let (apaOrigin, bytes) ← Alpha.decode 4 bytes
  let (tradeUniqueIdentifier, bytes) ← Alpha.decode 16 bytes
  pure ({ mdSeqNum, rebroadcastIndicator, emm, eventTime, tradingDateTime, publicationDateTime, tradeType, mifidInstrumentIdTypeOptional, mifidInstrumentIdOptional, mifidTransactionId, mifidPriceOptional, mifidQuantity, mifidPriceNotation, mifidCurrency, mifidQtyInMsrmtUnitNotation, mifidQuantityMeasurementUnit, mifidNotionalAmount, notionalCurrency, mifidClearingFlag, efficientMmtMarketMechanism, efficientMmtTradingMode, efficientMmtTransactionCategory, efficientMmtNegotiationIndicator, efficientMmtAgencyCrossTradeIndicator, efficientMmtModificationIndicator, efficientMmtBenchmarkIndicator, efficientMmtSpecialDividendIndicator, efficientMmtOffBookAutomatedIndicator, efficientMmtContributiontoPrice, efficientMmtAlgorithmicIndicator, efficientMmtPublicationMode, efficientMmtPostTradeDeferral, efficientMmtDuplicativeIndicator, tradeReference, originalReportTimestamp, priceMultiplier, priceMultiplierDecimals, venue, mifidEmissionAllowanceType, longTradeReference, apaOrigin, tradeUniqueIdentifier }, bytes)

@[simp] theorem encode_length (message : ApaFullTradeInformationMessage) : (encode message).length = 405 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, EfficientMmtTradingMode.encode_length, EfficientMmtTransactionCategory.encode_length, EfficientMmtNegotiationIndicator.encode_length, EfficientMmtAgencyCrossTradeIndicator.encode_length, EfficientMmtModificationIndicator.encode_length, EfficientMmtBenchmarkIndicator.encode_length, EfficientMmtSpecialDividendIndicator.encode_length, EfficientMmtOffBookAutomatedIndicator.encode_length, EfficientMmtContributiontoPrice.encode_length, EfficientMmtAlgorithmicIndicator.encode_length, EfficientMmtPublicationMode.encode_length, EfficientMmtPostTradeDeferral.encode_length, EfficientMmtDuplicativeIndicator.encode_length]

theorem encode_length_pos (message : ApaFullTradeInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ApaFullTradeInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtTradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtTransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtNegotiationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtAgencyCrossTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtModificationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtBenchmarkIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtSpecialDividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtOffBookAutomatedIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtContributiontoPrice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtAlgorithmicIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtPublicationMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtPostTradeDeferral.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfficientMmtDuplicativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end ApaFullTradeInformationMessage

/-- Interest Payment Date Rep Group: 2 bytes -/
structure InterestPaymentDateRepGroup where
  interestPaymentDate : BitVec 16
  deriving DecidableEq, Repr

namespace InterestPaymentDateRepGroup

def encode (message : InterestPaymentDateRepGroup) : List UInt8 :=
  encodeUIntLE 2 message.interestPaymentDate

def decode (bytes : List UInt8) : Option (InterestPaymentDateRepGroup × List UInt8) := do
  let (interestPaymentDate, bytes) ← decodeUIntLE 2 bytes
  pure ({ interestPaymentDate }, bytes)

@[simp] theorem encode_length (message : InterestPaymentDateRepGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : InterestPaymentDateRepGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InterestPaymentDateRepGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InterestPaymentDateRepGroup

/-- Interest Payment Date Rep Groups -/
structure InterestPaymentDateRepGroups where
  blockLengthShort : BitVec 8
  interestPaymentDateRepGroup : Bounded 1 InterestPaymentDateRepGroup
  deriving DecidableEq, Repr

namespace InterestPaymentDateRepGroups

def encode (message : InterestPaymentDateRepGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.interestPaymentDateRepGroup.val.length)
    ++ (encodeMany InterestPaymentDateRepGroup.encode message.interestPaymentDateRepGroup.val))

def decode (bytes : List UInt8) : Option (InterestPaymentDateRepGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (interestPaymentDateRepGroup_, bytes) ← decodeMany InterestPaymentDateRepGroup.decode numInGroup.toNat bytes
  if fits_interestPaymentDateRepGroup : interestPaymentDateRepGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, interestPaymentDateRepGroup := ⟨interestPaymentDateRepGroup_, fits_interestPaymentDateRepGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InterestPaymentDateRepGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InterestPaymentDateRepGroups) : (encode message).length ≤ 512 := by
  have bound_interestPaymentDateRepGroup := message.interestPaymentDateRepGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const InterestPaymentDateRepGroup.encode 2 InterestPaymentDateRepGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InterestPaymentDateRepGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InterestPaymentDateRepGroup.encode InterestPaymentDateRepGroup.decode InterestPaymentDateRepGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.interestPaymentDateRepGroup.length_lt]
  rfl

end InterestPaymentDateRepGroups

/-- Bf Instrument Reference Message -/
structure BfInstrumentReferenceMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  optiqSegment : BitVec 8
  isinCodeOptional : Alpha 12
  sedolCode : Alpha 7
  longIssuerName : Alpha 250
  longInstrumentName : Alpha 250
  currencyOptional : Alpha 3
  dateOfInitialListing : BitVec 16
  shareAmountInIssue : BitVec 64
  openedClosedFund : OpenedClosedFund
  lastNavPrice : BitVec 64
  grossOfCdscIndicator : GrossOfCdscIndicator
  coupon : BitVec 64
  maturityDateOptional : Alpha 8
  closingPrice : BitVec 64
  micOptional : Alpha 4
  grossDividendPayablePerUnit : BitVec 64
  dividendCurrency : Alpha 3
  dividendRecordDate : BitVec 16
  dividendRate : BitVec 64
  exDividendDate : BitVec 16
  dividendPaymentDate : BitVec 16
  taxDescriptionAttachingToADividend : TaxDescriptionAttachingToADividend
  nextMeeting : Alpha 8
  grossDividendInEuros : BitVec 64
  issueDate : BitVec 16
  issuingCountry : Alpha 3
  cfiOptional : Alpha 6
  paymentFrequency : BitVec 8
  minimumAmount : BitVec 64
  instrumentCategory : BitVec 8
  securityCondition : SecurityCondition
  mifidPriceNotation : Alpha 4
  priceIndexLevelDecimals : BitVec 8
  quantityDecimals : BitVec 8
  amountDecimals : BitVec 8
  ratioMultiplierDecimals : BitVec 8
  interestPaymentDateRepGroups : InterestPaymentDateRepGroups
  deriving DecidableEq, Repr

namespace BfInstrumentReferenceMessage

def encode (message : BfInstrumentReferenceMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUInt 1 message.optiqSegment
    ++ (Alpha.encode message.isinCodeOptional
    ++ (Alpha.encode message.sedolCode
    ++ (Alpha.encode message.longIssuerName
    ++ (Alpha.encode message.longInstrumentName
    ++ (Alpha.encode message.currencyOptional
    ++ (encodeUIntLE 2 message.dateOfInitialListing
    ++ (encodeUIntLE 8 message.shareAmountInIssue
    ++ (OpenedClosedFund.encode message.openedClosedFund
    ++ (encodeUIntLE 8 message.lastNavPrice
    ++ (GrossOfCdscIndicator.encode message.grossOfCdscIndicator
    ++ (encodeUIntLE 8 message.coupon
    ++ (Alpha.encode message.maturityDateOptional
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (Alpha.encode message.micOptional
    ++ (encodeUIntLE 8 message.grossDividendPayablePerUnit
    ++ (Alpha.encode message.dividendCurrency
    ++ (encodeUIntLE 2 message.dividendRecordDate
    ++ (encodeUIntLE 8 message.dividendRate
    ++ (encodeUIntLE 2 message.exDividendDate
    ++ (encodeUIntLE 2 message.dividendPaymentDate
    ++ (TaxDescriptionAttachingToADividend.encode message.taxDescriptionAttachingToADividend
    ++ (Alpha.encode message.nextMeeting
    ++ (encodeUIntLE 8 message.grossDividendInEuros
    ++ (encodeUIntLE 2 message.issueDate
    ++ (Alpha.encode message.issuingCountry
    ++ (Alpha.encode message.cfiOptional
    ++ (encodeUInt 1 message.paymentFrequency
    ++ (encodeUIntLE 8 message.minimumAmount
    ++ (encodeUInt 1 message.instrumentCategory
    ++ (SecurityCondition.encode message.securityCondition
    ++ (Alpha.encode message.mifidPriceNotation
    ++ (encodeUInt 1 message.priceIndexLevelDecimals
    ++ (encodeUInt 1 message.quantityDecimals
    ++ (encodeUInt 1 message.amountDecimals
    ++ (encodeUInt 1 message.ratioMultiplierDecimals
    ++ (InterestPaymentDateRepGroups.encode message.interestPaymentDateRepGroups)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BfInstrumentReferenceMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (optiqSegment, bytes) ← decodeUInt 1 bytes
  let (isinCodeOptional, bytes) ← Alpha.decode 12 bytes
  let (sedolCode, bytes) ← Alpha.decode 7 bytes
  let (longIssuerName, bytes) ← Alpha.decode 250 bytes
  let (longInstrumentName, bytes) ← Alpha.decode 250 bytes
  let (currencyOptional, bytes) ← Alpha.decode 3 bytes
  let (dateOfInitialListing, bytes) ← decodeUIntLE 2 bytes
  let (shareAmountInIssue, bytes) ← decodeUIntLE 8 bytes
  let (openedClosedFund, bytes) ← OpenedClosedFund.decode bytes
  let (lastNavPrice, bytes) ← decodeUIntLE 8 bytes
  let (grossOfCdscIndicator, bytes) ← GrossOfCdscIndicator.decode bytes
  let (coupon, bytes) ← decodeUIntLE 8 bytes
  let (maturityDateOptional, bytes) ← Alpha.decode 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (micOptional, bytes) ← Alpha.decode 4 bytes
  let (grossDividendPayablePerUnit, bytes) ← decodeUIntLE 8 bytes
  let (dividendCurrency, bytes) ← Alpha.decode 3 bytes
  let (dividendRecordDate, bytes) ← decodeUIntLE 2 bytes
  let (dividendRate, bytes) ← decodeUIntLE 8 bytes
  let (exDividendDate, bytes) ← decodeUIntLE 2 bytes
  let (dividendPaymentDate, bytes) ← decodeUIntLE 2 bytes
  let (taxDescriptionAttachingToADividend, bytes) ← TaxDescriptionAttachingToADividend.decode bytes
  let (nextMeeting, bytes) ← Alpha.decode 8 bytes
  let (grossDividendInEuros, bytes) ← decodeUIntLE 8 bytes
  let (issueDate, bytes) ← decodeUIntLE 2 bytes
  let (issuingCountry, bytes) ← Alpha.decode 3 bytes
  let (cfiOptional, bytes) ← Alpha.decode 6 bytes
  let (paymentFrequency, bytes) ← decodeUInt 1 bytes
  let (minimumAmount, bytes) ← decodeUIntLE 8 bytes
  let (instrumentCategory, bytes) ← decodeUInt 1 bytes
  let (securityCondition, bytes) ← SecurityCondition.decode bytes
  let (mifidPriceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceIndexLevelDecimals, bytes) ← decodeUInt 1 bytes
  let (quantityDecimals, bytes) ← decodeUInt 1 bytes
  let (amountDecimals, bytes) ← decodeUInt 1 bytes
  let (ratioMultiplierDecimals, bytes) ← decodeUInt 1 bytes
  let (interestPaymentDateRepGroups, bytes) ← InterestPaymentDateRepGroups.decode bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, symbolIndex, optiqSegment, isinCodeOptional, sedolCode, longIssuerName, longInstrumentName, currencyOptional, dateOfInitialListing, shareAmountInIssue, openedClosedFund, lastNavPrice, grossOfCdscIndicator, coupon, maturityDateOptional, closingPrice, micOptional, grossDividendPayablePerUnit, dividendCurrency, dividendRecordDate, dividendRate, exDividendDate, dividendPaymentDate, taxDescriptionAttachingToADividend, nextMeeting, grossDividendInEuros, issueDate, issuingCountry, cfiOptional, paymentFrequency, minimumAmount, instrumentCategory, securityCondition, mifidPriceNotation, priceIndexLevelDecimals, quantityDecimals, amountDecimals, ratioMultiplierDecimals, interestPaymentDateRepGroups }, bytes)

theorem encode_length_pos (message : BfInstrumentReferenceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BfInstrumentReferenceMessage) : (encode message).length ≤ 1168 := by
  have bound_interestPaymentDateRepGroups := InterestPaymentDateRepGroups.encode_length_le message.interestPaymentDateRepGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OpenedClosedFund.encode_length, GrossOfCdscIndicator.encode_length, TaxDescriptionAttachingToADividend.encode_length, SecurityCondition.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BfInstrumentReferenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpenedClosedFund.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, GrossOfCdscIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TaxDescriptionAttachingToADividend.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityCondition.decode_encode, some_bind]
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
  rw [InterestPaymentDateRepGroups.decode_encode, some_bind]
  rfl

end BfInstrumentReferenceMessage

/-- Bf Trade Message: 148 bytes -/
structure BfTradeMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  mifidTransactionId : Alpha 52
  eventTime : BitVec 64
  bidOfferDateTime : BitVec 64
  mmtModificationIndicator : Alpha 4
  price : BitVec 64
  bidPrice : BitVec 64
  offerPrice : BitVec 64
  quantity : BitVec 64
  mmtAgencyCrossTradeIndicator : Alpha 4
  mmtBenchmarkIndicator : Alpha 4
  mmtSpecialDividendIndicator : Alpha 4
  mmtTradingMode : MmtTradingMode
  mifidPriceNotation : Alpha 4
  quantityNotation : Alpha 3
  notionalAmountTraded : BitVec 64
  tradingCurrencyOptional : Alpha 3
  deriving DecidableEq, Repr

namespace BfTradeMessage

def encode (message : BfTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.mifidTransactionId
    ++ (encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 8 message.bidOfferDateTime
    ++ (Alpha.encode message.mmtModificationIndicator
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 8 message.offerPrice
    ++ (encodeUIntLE 8 message.quantity
    ++ (Alpha.encode message.mmtAgencyCrossTradeIndicator
    ++ (Alpha.encode message.mmtBenchmarkIndicator
    ++ (Alpha.encode message.mmtSpecialDividendIndicator
    ++ (MmtTradingMode.encode message.mmtTradingMode
    ++ (Alpha.encode message.mifidPriceNotation
    ++ (Alpha.encode message.quantityNotation
    ++ (encodeUIntLE 8 message.notionalAmountTraded
    ++ (Alpha.encode message.tradingCurrencyOptional))))))))))))))))))

def decode (bytes : List UInt8) : Option (BfTradeMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (mifidTransactionId, bytes) ← Alpha.decode 52 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (bidOfferDateTime, bytes) ← decodeUIntLE 8 bytes
  let (mmtModificationIndicator, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (offerPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (mmtAgencyCrossTradeIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtBenchmarkIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtSpecialDividendIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtTradingMode, bytes) ← MmtTradingMode.decode bytes
  let (mifidPriceNotation, bytes) ← Alpha.decode 4 bytes
  let (quantityNotation, bytes) ← Alpha.decode 3 bytes
  let (notionalAmountTraded, bytes) ← decodeUIntLE 8 bytes
  let (tradingCurrencyOptional, bytes) ← Alpha.decode 3 bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, symbolIndex, mifidTransactionId, eventTime, bidOfferDateTime, mmtModificationIndicator, price, bidPrice, offerPrice, quantity, mmtAgencyCrossTradeIndicator, mmtBenchmarkIndicator, mmtSpecialDividendIndicator, mmtTradingMode, mifidPriceNotation, quantityNotation, notionalAmountTraded, tradingCurrencyOptional }, bytes)

@[simp] theorem encode_length (message : BfTradeMessage) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, MmtTradingMode.encode_length]

theorem encode_length_pos (message : BfTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BfTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MmtTradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BfTradeMessage

/-- Bfnav Message: 109 bytes -/
structure BfnavMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  bidOfferDateTime : BitVec 64
  mifidTransactionId : Alpha 52
  mmtModificationIndicator : Alpha 4
  navPrice : BitVec 64
  eventTimeOptional : BitVec 64
  navBidPrice : BitVec 64
  navOfferPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BfnavMessage

def encode (message : BfnavMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.bidOfferDateTime
    ++ (Alpha.encode message.mifidTransactionId
    ++ (Alpha.encode message.mmtModificationIndicator
    ++ (encodeUIntLE 8 message.navPrice
    ++ (encodeUIntLE 8 message.eventTimeOptional
    ++ (encodeUIntLE 8 message.navBidPrice
    ++ (encodeUIntLE 8 message.navOfferPrice)))))))))

def decode (bytes : List UInt8) : Option (BfnavMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (bidOfferDateTime, bytes) ← decodeUIntLE 8 bytes
  let (mifidTransactionId, bytes) ← Alpha.decode 52 bytes
  let (mmtModificationIndicator, bytes) ← Alpha.decode 4 bytes
  let (navPrice, bytes) ← decodeUIntLE 8 bytes
  let (eventTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (navBidPrice, bytes) ← decodeUIntLE 8 bytes
  let (navOfferPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, symbolIndex, bidOfferDateTime, mifidTransactionId, mmtModificationIndicator, navPrice, eventTimeOptional, navBidPrice, navOfferPrice }, bytes)

@[simp] theorem encode_length (message : BfnavMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BfnavMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BfnavMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BfnavMessage

/-- Bf Instrument Suspension Message: 22 bytes -/
structure BfInstrumentSuspensionMessage where
  mdSeqNumOptional : BitVec 64
  rebroadcastIndicator : BitVec 8
  symbolIndex : BitVec 32
  eventTime : BitVec 64
  securityCondition : SecurityCondition
  deriving DecidableEq, Repr

namespace BfInstrumentSuspensionMessage

def encode (message : BfInstrumentSuspensionMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdSeqNumOptional
    ++ (encodeUInt 1 message.rebroadcastIndicator
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 8 message.eventTime
    ++ (SecurityCondition.encode message.securityCondition))))

def decode (bytes : List UInt8) : Option (BfInstrumentSuspensionMessage × List UInt8) := do
  let (mdSeqNumOptional, bytes) ← decodeUIntLE 8 bytes
  let (rebroadcastIndicator, bytes) ← decodeUInt 1 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (securityCondition, bytes) ← SecurityCondition.decode bytes
  pure ({ mdSeqNumOptional, rebroadcastIndicator, symbolIndex, eventTime, securityCondition }, bytes)

@[simp] theorem encode_length (message : BfInstrumentSuspensionMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, SecurityCondition.encode_length]

theorem encode_length_pos (message : BfInstrumentSuspensionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BfInstrumentSuspensionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SecurityCondition.decode_encode, some_bind]
  rfl

end BfInstrumentSuspensionMessage

/-- Start Of Snapshot Message: 16 bytes -/
structure StartOfSnapshotMessage where
  lastMdSeqNum : BitVec 64
  snapshotTime : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfSnapshotMessage

def encode (message : StartOfSnapshotMessage) : List UInt8 :=
  encodeUIntLE 8 message.lastMdSeqNum
    ++ (encodeUIntLE 8 message.snapshotTime)

def decode (bytes : List UInt8) : Option (StartOfSnapshotMessage × List UInt8) := do
  let (lastMdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (snapshotTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ lastMdSeqNum, snapshotTime }, bytes)

@[simp] theorem encode_length (message : StartOfSnapshotMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StartOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StartOfSnapshotMessage

/-- End Of Snapshot Message: 16 bytes -/
structure EndOfSnapshotMessage where
  lastMdSeqNum : BitVec 64
  snapshotTime : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  encodeUIntLE 8 message.lastMdSeqNum
    ++ (encodeUIntLE 8 message.snapshotTime)

def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (lastMdSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (snapshotTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ lastMdSeqNum, snapshotTime }, bytes)

@[simp] theorem encode_length (message : EndOfSnapshotMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EndOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EndOfSnapshotMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | startOfDayMessage (message : StartOfDayMessage) -- 1101
  | endOfDayMessage (message : EndOfDayMessage) -- 1102
  | healthStatusMessage (message : HealthStatusMessage) -- 1103
  | technicalNotificationMessage (message : TechnicalNotificationMessage) -- 1106
  | marketUpdateMessage (message : MarketUpdateMessage) -- 1001
  | orderUpdateMessage (message : OrderUpdateMessage) -- 1002
  | priceUpdateMessage (message : PriceUpdateMessage) -- 1003
  | fullTradeInformationMessage (message : FullTradeInformationMessage) -- 1004
  | marketStatusChangeMessage (message : MarketStatusChangeMessage) -- 1005
  | timetableMessage (message : TimetableMessage) -- 1006
  | standingDataMessage (message : StandingDataMessage) -- 1007
  | realTimeIndexMessage (message : RealTimeIndexMessage) -- 1008
  | statisticsMessage (message : StatisticsMessage) -- 1009
  | indexSummaryMessage (message : IndexSummaryMessage) -- 1011
  | strategyStandingDataMessage (message : StrategyStandingDataMessage) -- 1012
  | contractStandingDataMessage (message : ContractStandingDataMessage) -- 1013
  | outrightStandingDataMessage (message : OutrightStandingDataMessage) -- 1014
  | longOrderUpdateMessage (message : LongOrderUpdateMessage) -- 1015
  | lisPackageStructureMessage (message : LisPackageStructureMessage) -- 1016
  | apaQuotesMessage (message : ApaQuotesMessage) -- 1026
  | apaStandingDataMessage (message : ApaStandingDataMessage) -- 1027
  | apaFullTradeInformationMessage (message : ApaFullTradeInformationMessage) -- 1028
  | bfInstrumentReferenceMessage (message : BfInstrumentReferenceMessage) -- 1201
  | bfTradeMessage (message : BfTradeMessage) -- 1202
  | bfnavMessage (message : BfnavMessage) -- 1203
  | bfInstrumentSuspensionMessage (message : BfInstrumentSuspensionMessage) -- 1204
  | startOfSnapshotMessage (message : StartOfSnapshotMessage) -- 2101
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- 2102
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .startOfDayMessage _ => 1101
  | .endOfDayMessage _ => 1102
  | .healthStatusMessage _ => 1103
  | .technicalNotificationMessage _ => 1106
  | .marketUpdateMessage _ => 1001
  | .orderUpdateMessage _ => 1002
  | .priceUpdateMessage _ => 1003
  | .fullTradeInformationMessage _ => 1004
  | .marketStatusChangeMessage _ => 1005
  | .timetableMessage _ => 1006
  | .standingDataMessage _ => 1007
  | .realTimeIndexMessage _ => 1008
  | .statisticsMessage _ => 1009
  | .indexSummaryMessage _ => 1011
  | .strategyStandingDataMessage _ => 1012
  | .contractStandingDataMessage _ => 1013
  | .outrightStandingDataMessage _ => 1014
  | .longOrderUpdateMessage _ => 1015
  | .lisPackageStructureMessage _ => 1016
  | .apaQuotesMessage _ => 1026
  | .apaStandingDataMessage _ => 1027
  | .apaFullTradeInformationMessage _ => 1028
  | .bfInstrumentReferenceMessage _ => 1201
  | .bfTradeMessage _ => 1202
  | .bfnavMessage _ => 1203
  | .bfInstrumentSuspensionMessage _ => 1204
  | .startOfSnapshotMessage _ => 2101
  | .endOfSnapshotMessage _ => 2102

def encode : Payload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .healthStatusMessage message => HealthStatusMessage.encode message
  | .technicalNotificationMessage message => TechnicalNotificationMessage.encode message
  | .marketUpdateMessage message => MarketUpdateMessage.encode message
  | .orderUpdateMessage message => OrderUpdateMessage.encode message
  | .priceUpdateMessage message => PriceUpdateMessage.encode message
  | .fullTradeInformationMessage message => FullTradeInformationMessage.encode message
  | .marketStatusChangeMessage message => MarketStatusChangeMessage.encode message
  | .timetableMessage message => TimetableMessage.encode message
  | .standingDataMessage message => StandingDataMessage.encode message
  | .realTimeIndexMessage message => RealTimeIndexMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .indexSummaryMessage message => IndexSummaryMessage.encode message
  | .strategyStandingDataMessage message => StrategyStandingDataMessage.encode message
  | .contractStandingDataMessage message => ContractStandingDataMessage.encode message
  | .outrightStandingDataMessage message => OutrightStandingDataMessage.encode message
  | .longOrderUpdateMessage message => LongOrderUpdateMessage.encode message
  | .lisPackageStructureMessage message => LisPackageStructureMessage.encode message
  | .apaQuotesMessage message => ApaQuotesMessage.encode message
  | .apaStandingDataMessage message => ApaStandingDataMessage.encode message
  | .apaFullTradeInformationMessage message => ApaFullTradeInformationMessage.encode message
  | .bfInstrumentReferenceMessage message => BfInstrumentReferenceMessage.encode message
  | .bfTradeMessage message => BfTradeMessage.encode message
  | .bfnavMessage message => BfnavMessage.encode message
  | .bfInstrumentSuspensionMessage message => BfInstrumentSuspensionMessage.encode message
  | .startOfSnapshotMessage message => StartOfSnapshotMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 12515 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | healthStatusMessage inner =>
    simp only [encode, HealthStatusMessage.encode_length]
    omega
  | technicalNotificationMessage inner =>
    simp only [encode, TechnicalNotificationMessage.encode_length]
    omega
  | marketUpdateMessage inner =>
    have bound_inner := MarketUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderUpdateMessage inner =>
    have bound_inner := OrderUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | priceUpdateMessage inner =>
    have bound_inner := PriceUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | fullTradeInformationMessage inner =>
    simp only [encode, FullTradeInformationMessage.encode_length]
    omega
  | marketStatusChangeMessage inner =>
    have bound_inner := MarketStatusChangeMessage.encode_length_le inner
    simp only [encode]
    omega
  | timetableMessage inner =>
    have bound_inner := TimetableMessage.encode_length_le inner
    simp only [encode]
    omega
  | standingDataMessage inner =>
    have bound_inner := StandingDataMessage.encode_length_le inner
    simp only [encode]
    omega
  | realTimeIndexMessage inner =>
    simp only [encode, RealTimeIndexMessage.encode_length]
    omega
  | statisticsMessage inner =>
    have bound_inner := StatisticsMessage.encode_length_le inner
    simp only [encode]
    omega
  | indexSummaryMessage inner =>
    simp only [encode, IndexSummaryMessage.encode_length]
    omega
  | strategyStandingDataMessage inner =>
    have bound_inner := StrategyStandingDataMessage.encode_length_le inner
    simp only [encode]
    omega
  | contractStandingDataMessage inner =>
    have bound_inner := ContractStandingDataMessage.encode_length_le inner
    simp only [encode]
    omega
  | outrightStandingDataMessage inner =>
    have bound_inner := OutrightStandingDataMessage.encode_length_le inner
    simp only [encode]
    omega
  | longOrderUpdateMessage inner =>
    have bound_inner := LongOrderUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | lisPackageStructureMessage inner =>
    have bound_inner := LisPackageStructureMessage.encode_length_le inner
    simp only [encode]
    omega
  | apaQuotesMessage inner =>
    simp only [encode, ApaQuotesMessage.encode_length]
    omega
  | apaStandingDataMessage inner =>
    simp only [encode, ApaStandingDataMessage.encode_length]
    omega
  | apaFullTradeInformationMessage inner =>
    simp only [encode, ApaFullTradeInformationMessage.encode_length]
    omega
  | bfInstrumentReferenceMessage inner =>
    have bound_inner := BfInstrumentReferenceMessage.encode_length_le inner
    simp only [encode]
    omega
  | bfTradeMessage inner =>
    simp only [encode, BfTradeMessage.encode_length]
    omega
  | bfnavMessage inner =>
    simp only [encode, BfnavMessage.encode_length]
    omega
  | bfInstrumentSuspensionMessage inner =>
    simp only [encode, BfInstrumentSuspensionMessage.encode_length]
    omega
  | startOfSnapshotMessage inner =>
    simp only [encode, StartOfSnapshotMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [encode, EndOfSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1101 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 1102 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 1103 then (HealthStatusMessage.decode bytes).map fun (message, rest) => (.healthStatusMessage message, rest)
  else if tag = 1106 then (TechnicalNotificationMessage.decode bytes).map fun (message, rest) => (.technicalNotificationMessage message, rest)
  else if tag = 1001 then (MarketUpdateMessage.decode bytes).map fun (message, rest) => (.marketUpdateMessage message, rest)
  else if tag = 1002 then (OrderUpdateMessage.decode bytes).map fun (message, rest) => (.orderUpdateMessage message, rest)
  else if tag = 1003 then (PriceUpdateMessage.decode bytes).map fun (message, rest) => (.priceUpdateMessage message, rest)
  else if tag = 1004 then (FullTradeInformationMessage.decode bytes).map fun (message, rest) => (.fullTradeInformationMessage message, rest)
  else if tag = 1005 then (MarketStatusChangeMessage.decode bytes).map fun (message, rest) => (.marketStatusChangeMessage message, rest)
  else if tag = 1006 then (TimetableMessage.decode bytes).map fun (message, rest) => (.timetableMessage message, rest)
  else if tag = 1007 then (StandingDataMessage.decode bytes).map fun (message, rest) => (.standingDataMessage message, rest)
  else if tag = 1008 then (RealTimeIndexMessage.decode bytes).map fun (message, rest) => (.realTimeIndexMessage message, rest)
  else if tag = 1009 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 1011 then (IndexSummaryMessage.decode bytes).map fun (message, rest) => (.indexSummaryMessage message, rest)
  else if tag = 1012 then (StrategyStandingDataMessage.decode bytes).map fun (message, rest) => (.strategyStandingDataMessage message, rest)
  else if tag = 1013 then (ContractStandingDataMessage.decode bytes).map fun (message, rest) => (.contractStandingDataMessage message, rest)
  else if tag = 1014 then (OutrightStandingDataMessage.decode bytes).map fun (message, rest) => (.outrightStandingDataMessage message, rest)
  else if tag = 1015 then (LongOrderUpdateMessage.decode bytes).map fun (message, rest) => (.longOrderUpdateMessage message, rest)
  else if tag = 1016 then (LisPackageStructureMessage.decode bytes).map fun (message, rest) => (.lisPackageStructureMessage message, rest)
  else if tag = 1026 then (ApaQuotesMessage.decode bytes).map fun (message, rest) => (.apaQuotesMessage message, rest)
  else if tag = 1027 then (ApaStandingDataMessage.decode bytes).map fun (message, rest) => (.apaStandingDataMessage message, rest)
  else if tag = 1028 then (ApaFullTradeInformationMessage.decode bytes).map fun (message, rest) => (.apaFullTradeInformationMessage message, rest)
  else if tag = 1201 then (BfInstrumentReferenceMessage.decode bytes).map fun (message, rest) => (.bfInstrumentReferenceMessage message, rest)
  else if tag = 1202 then (BfTradeMessage.decode bytes).map fun (message, rest) => (.bfTradeMessage message, rest)
  else if tag = 1203 then (BfnavMessage.decode bytes).map fun (message, rest) => (.bfnavMessage message, rest)
  else if tag = 1204 then (BfInstrumentSuspensionMessage.decode bytes).map fun (message, rest) => (.bfInstrumentSuspensionMessage message, rest)
  else if tag = 2101 then (StartOfSnapshotMessage.decode bytes).map fun (message, rest) => (.startOfSnapshotMessage message, rest)
  else if tag = 2102 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Optiq Message -/
structure OptiqMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace OptiqMessage

def encodeBody (message : OptiqMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decodeBody (bytes : List UInt8) : Option (OptiqMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : OptiqMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OptiqMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | startOfDayMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfDayMessage.encode_length]
    omega
  | healthStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HealthStatusMessage.encode_length]
    omega
  | technicalNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TechnicalNotificationMessage.encode_length]
    omega
  | marketUpdateMessage inner =>
    have bound_inner := MarketUpdateMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | orderUpdateMessage inner =>
    have bound_inner := OrderUpdateMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | priceUpdateMessage inner =>
    have bound_inner := PriceUpdateMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | fullTradeInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FullTradeInformationMessage.encode_length]
    omega
  | marketStatusChangeMessage inner =>
    have bound_inner := MarketStatusChangeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | timetableMessage inner =>
    have bound_inner := TimetableMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | standingDataMessage inner =>
    have bound_inner := StandingDataMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | realTimeIndexMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RealTimeIndexMessage.encode_length]
    omega
  | statisticsMessage inner =>
    have bound_inner := StatisticsMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | indexSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexSummaryMessage.encode_length]
    omega
  | strategyStandingDataMessage inner =>
    have bound_inner := StrategyStandingDataMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | contractStandingDataMessage inner =>
    have bound_inner := ContractStandingDataMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | outrightStandingDataMessage inner =>
    have bound_inner := OutrightStandingDataMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | longOrderUpdateMessage inner =>
    have bound_inner := LongOrderUpdateMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | lisPackageStructureMessage inner =>
    have bound_inner := LisPackageStructureMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | apaQuotesMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ApaQuotesMessage.encode_length]
    omega
  | apaStandingDataMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ApaStandingDataMessage.encode_length]
    omega
  | apaFullTradeInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ApaFullTradeInformationMessage.encode_length]
    omega
  | bfInstrumentReferenceMessage inner =>
    have bound_inner := BfInstrumentReferenceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | bfTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BfTradeMessage.encode_length]
    omega
  | bfnavMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BfnavMessage.encode_length]
    omega
  | bfInstrumentSuspensionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BfInstrumentSuspensionMessage.encode_length]
    omega
  | startOfSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSnapshotMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSnapshotMessage.encode_length]
    omega

/-- Size rule: Frame counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : OptiqMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (OptiqMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : OptiqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OptiqMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end OptiqMessage

/-- Optiq Message -/
structure OptiqMessagePlain where
  optiqMessage : List OptiqMessage
  deriving DecidableEq, Repr

namespace OptiqMessagePlain

def encode (message : OptiqMessagePlain) : List UInt8 :=
  encodeMany OptiqMessage.encode message.optiqMessage

def decode (bytes : List UInt8) : Option OptiqMessagePlain := do
  let optiqMessage ← decodeAll OptiqMessage.decode bytes.length bytes
  pure { optiqMessage }

theorem decode_encode (message : OptiqMessagePlain) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany OptiqMessage.encode OptiqMessage.decode OptiqMessage.decode_encode OptiqMessage.encode_length_pos message.optiqMessage _ (encodeMany_length_ge OptiqMessage.encode OptiqMessage.encode_length_pos message.optiqMessage), some_bind]
  rfl

end OptiqMessagePlain

/-- Optiq Message -/
structure OptiqMessageLz4 where
  payload : List UInt8
  deriving DecidableEq, Repr

namespace OptiqMessageLz4

def encode (message : OptiqMessageLz4) : List UInt8 :=
  encodeMany Byte.encode message.payload

def decode (bytes : List UInt8) : Option OptiqMessageLz4 := do
  let payload ← decodeAll Byte.decode bytes.length bytes
  pure { payload }

theorem decode_encode (message : OptiqMessageLz4) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.payload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.payload), some_bind]
  rfl

end OptiqMessageLz4

/-- The Optiq Message, as it lies when Compression says it was not LZ4 transformed and as bytes when it says it was -/
inductive OptiqMessageBody where
  | plain (message : OptiqMessagePlain) -- 0
  | lz4 (message : OptiqMessageLz4) -- 1
  deriving DecidableEq, Repr

namespace OptiqMessageBody

/-- The Compression each message is sent under -/
def tag : OptiqMessageBody → BitVec 16
  | .plain _ => 0
  | .lz4 _ => 1

/-- The tag is written into its own bits of the field that carries it, and no others -/
theorem tag_inside (message : OptiqMessageBody) : tag message &&& 65534 = 0 := by
  cases message <;> (simp only [tag]; decide)

def encode : OptiqMessageBody → List UInt8
  | .plain message => OptiqMessagePlain.encode message
  | .lz4 message => OptiqMessageLz4.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option OptiqMessageBody :=
  if tag = 0 then (OptiqMessagePlain.decode bytes).map fun message => .plain message
  else if tag = 1 then (OptiqMessageLz4.decode bytes).map fun message => .lz4 message
  else none

theorem decode_encode (message : OptiqMessageBody) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | plain message => simp [decode, encode, tag, OptiqMessagePlain.decode_encode]
  | lz4 message => simp [decode, encode, tag, OptiqMessageLz4.decode_encode]

end OptiqMessageBody

/-- Packet -/
structure Packet where
  packetTime : BitVec 64
  packetSequenceNumber : BitVec 32
  packetFlags : Masked 16 1
  channelId : BitVec 16
  optiqMessage : OptiqMessageBody
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 8 message.packetTime
    ++ (encodeUIntLE 4 message.packetSequenceNumber
    ++ (encodeUIntLE 2 (message.packetFlags.val ||| OptiqMessageBody.tag message.optiqMessage)
    ++ (encodeUIntLE 2 message.channelId
    ++ (OptiqMessageBody.encode message.optiqMessage))))

def decode (bytes : List UInt8) : Option Packet := do
  let (packetTime, bytes) ← decodeUIntLE 8 bytes
  let (packetSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (packetFlags_, bytes) ← decodeUIntLE 2 bytes
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let optiqMessage ← OptiqMessageBody.decode (packetFlags_ &&& 1) bytes
  if fits_packetFlags : (packetFlags_ &&& 65534) &&& 1 = 0 then
    pure { packetTime, packetSequenceNumber, packetFlags := ⟨packetFlags_ &&& 65534, fits_packetFlags⟩, channelId, optiqMessage }
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  have selected_packetFlags : (message.packetFlags.val ||| OptiqMessageBody.tag message.optiqMessage) &&& 1 = OptiqMessageBody.tag message.optiqMessage := by
    have clear := message.packetFlags.property
    have inside := OptiqMessageBody.tag_inside message.optiqMessage
    bv_decide
  have carried_packetFlags : (message.packetFlags.val ||| OptiqMessageBody.tag message.optiqMessage) &&& 65534 = message.packetFlags.val := by
    have clear := message.packetFlags.property
    have inside := OptiqMessageBody.tag_inside message.optiqMessage
    bv_decide
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_packetFlags]
  rw [OptiqMessageBody.decode_encode, some_bind]
  rw [dite_eq_left (by rw [carried_packetFlags]; exact message.packetFlags.property)]
  simp only [carried_packetFlags]
  rfl

end Packet

end Omi.EuronextOptiqMarketdatagatewaySbeV519
