import Omi.Wire

/-!
# Miami International Holdings Complex Top of Market v1.0.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Application Message is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Sesm Tcp Packet's body has no bound its 2 byte Sesm Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxEmeraldoptionsComplextopofmarketMachV10ATcp

/-- Refresh Message Type: one byte code -/
def RefreshMessageType.codes : List UInt8 :=
  [0x50, 0x43, 0x54, 0x55, 0x53]

inductive RefreshMessageType where
  | simpleSeriesUpdateRefresh -- Simple Series Update Refresh
  | complexStrategyUpdateRefresh -- Complex Strategy Update Refresh
  | topOfStrategyMarketRefresh -- Top Of Strategy Market Refresh
  | underlyingTradingStatusRefresh -- Underlying Trading Status Refresh
  | systemStateRefresh -- System State Refresh
  | unlisted (byte : { byte : UInt8 // byte ∉ RefreshMessageType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RefreshMessageType

def toByte : RefreshMessageType → UInt8
  | .simpleSeriesUpdateRefresh => 0x50
  | .complexStrategyUpdateRefresh => 0x43
  | .topOfStrategyMarketRefresh => 0x54
  | .underlyingTradingStatusRefresh => 0x55
  | .systemStateRefresh => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RefreshMessageType :=
  if byte = 0x50 then .simpleSeriesUpdateRefresh
  else if byte = 0x43 then .complexStrategyUpdateRefresh
  else if byte = 0x54 then .topOfStrategyMarketRefresh
  else if byte = 0x55 then .underlyingTradingStatusRefresh
  else .systemStateRefresh

def ofByte (byte : UInt8) : RefreshMessageType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RefreshMessageType) : ofByte value.toByte = value := by
  cases value with
  | simpleSeriesUpdateRefresh => decide
  | complexStrategyUpdateRefresh => decide
  | topOfStrategyMarketRefresh => decide
  | underlyingTradingStatusRefresh => decide
  | systemStateRefresh => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RefreshMessageType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RefreshMessageType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RefreshMessageType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RefreshMessageType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RefreshMessageType

/-- Call Or Put: one byte code -/
def CallOrPut.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallOrPut where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallOrPut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallOrPut

def toByte : CallOrPut → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallOrPut :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallOrPut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallOrPut) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallOrPut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallOrPut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallOrPut) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CallOrPut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallOrPut

/-- Restricted Option: one byte code -/
def RestrictedOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RestrictedOption where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RestrictedOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RestrictedOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RestrictedOption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RestrictedOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RestrictedOption

/-- Long Term Option: one byte code -/
def LongTermOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LongTermOption where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LongTermOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LongTermOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LongTermOption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LongTermOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LongTermOption

/-- Active On Emerald: one byte code -/
def ActiveOnEmerald.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnEmerald where
  | active -- Active
  | inactive -- Inactive
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnEmerald.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnEmerald

def toByte : ActiveOnEmerald → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnEmerald :=
  if byte = 0x41 then .active
  else .inactive

def ofByte (byte : UInt8) : ActiveOnEmerald :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnEmerald) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnEmerald) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnEmerald × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnEmerald) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ActiveOnEmerald) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnEmerald

/-- Emerald Bbo Posting Increment Indicator: one byte code -/
def EmeraldBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive EmeraldBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ EmeraldBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EmeraldBboPostingIncrementIndicator

def toByte : EmeraldBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EmeraldBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : EmeraldBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EmeraldBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EmeraldBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EmeraldBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EmeraldBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EmeraldBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EmeraldBboPostingIncrementIndicator

/-- Liquidity Acceptance Increment Indicator: one byte code -/
def LiquidityAcceptanceIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive LiquidityAcceptanceIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityAcceptanceIncrementIndicator

def toByte : LiquidityAcceptanceIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityAcceptanceIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityAcceptanceIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityAcceptanceIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityAcceptanceIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityAcceptanceIncrementIndicator

/-- Opening Underlying Market Code: one byte code -/
def OpeningUnderlyingMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nationalStockExchange -- National Stock Exchange
  | finraAdf -- Finra Adf
  | marketIndependent -- Market Independent
  | miaxPearlEquities -- Miax Pearl Equities
  | internationalSecuritiesExchange -- International Securities Exchange
  | edgaExchangeInc -- Edga Exchange Inc
  | edgxExchangeInc -- Edgx Exchange Inc
  | ltse -- Ltse
  | chicagoStockExchange -- Chicago Stock Exchange
  | nyseEuronext -- Nyse Euronext
  | nyseArcaExchange -- Nyse Arca Exchange
  | nasdaqOmxViaUtpFeed -- Nasdaq Omx Via Utp Feed
  | nasdaqOmxViaCtaFeed -- Nasdaq Omx Via Cta Feed
  | memx -- Memx
  | iex -- Iex
  | cboeStockExchangeCbsx -- Cboe Stock Exchange Cbsx
  | nasdaqOmxPhlx -- Nasdaq Omx Phlx
  | batsYExchangeInc -- Bats Y Exchange Inc
  | batsExchangeInc -- Bats Exchange Inc
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningUnderlyingMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningUnderlyingMarketCode

def toByte : OpeningUnderlyingMarketCode → UInt8
  | .nyseAmex => 0x41
  | .nasdaqOmxBx => 0x42
  | .nationalStockExchange => 0x43
  | .finraAdf => 0x44
  | .marketIndependent => 0x45
  | .miaxPearlEquities => 0x48
  | .internationalSecuritiesExchange => 0x49
  | .edgaExchangeInc => 0x4A
  | .edgxExchangeInc => 0x4B
  | .ltse => 0x4C
  | .chicagoStockExchange => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArcaExchange => 0x50
  | .nasdaqOmxViaUtpFeed => 0x51
  | .nasdaqOmxViaCtaFeed => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cboeStockExchangeCbsx => 0x57
  | .nasdaqOmxPhlx => 0x58
  | .batsYExchangeInc => 0x59
  | .batsExchangeInc => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nationalStockExchange
  else if byte = 0x44 then .finraAdf
  else if byte = 0x45 then .marketIndependent
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .internationalSecuritiesExchange
  else if byte = 0x4A then .edgaExchangeInc
  else if byte = 0x4B then .edgxExchangeInc
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .chicagoStockExchange
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArcaExchange
  else if byte = 0x51 then .nasdaqOmxViaUtpFeed
  else if byte = 0x54 then .nasdaqOmxViaCtaFeed
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cboeStockExchangeCbsx
  else if byte = 0x58 then .nasdaqOmxPhlx
  else if byte = 0x59 then .batsYExchangeInc
  else .batsExchangeInc

def ofByte (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningUnderlyingMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmex => decide
  | nasdaqOmxBx => decide
  | nationalStockExchange => decide
  | finraAdf => decide
  | marketIndependent => decide
  | miaxPearlEquities => decide
  | internationalSecuritiesExchange => decide
  | edgaExchangeInc => decide
  | edgxExchangeInc => decide
  | ltse => decide
  | chicagoStockExchange => decide
  | nyseEuronext => decide
  | nyseArcaExchange => decide
  | nasdaqOmxViaUtpFeed => decide
  | nasdaqOmxViaCtaFeed => decide
  | memx => decide
  | iex => decide
  | cboeStockExchangeCbsx => decide
  | nasdaqOmxPhlx => decide
  | batsYExchangeInc => decide
  | batsExchangeInc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningUnderlyingMarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningUnderlyingMarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningUnderlyingMarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningUnderlyingMarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningUnderlyingMarketCode

/-- Update Reason: one byte code -/
def UpdateReason.codes : List UInt8 :=
  [0x4E, 0x55]

inductive UpdateReason where
  | newStrategyCreated -- New Strategy Created
  | updated -- Updated
  | unlisted (byte : { byte : UInt8 // byte ∉ UpdateReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UpdateReason

def toByte : UpdateReason → UInt8
  | .newStrategyCreated => 0x4E
  | .updated => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UpdateReason :=
  if byte = 0x4E then .newStrategyCreated
  else .updated

def ofByte (byte : UInt8) : UpdateReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UpdateReason) : ofByte value.toByte = value := by
  cases value with
  | newStrategyCreated => decide
  | updated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UpdateReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UpdateReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UpdateReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UpdateReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UpdateReason

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive LegSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | startTestSession -- Start Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startTestSession => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Condition: one byte code -/
def Condition.codes : List UInt8 :=
  [0x41, 0x54, 0x57, 0x53, 0x43, 0x4D, 0x4C]

inductive Condition where
  | regular -- Regular
  | tradingHalt -- Trading Halt
  | wide -- Wide
  | simpleAuction -- Simple Auction
  | complexAuction -- Complex Auction
  | simpleMarketProtection -- Simple Market Protection
  | legMarketProtection -- Leg Market Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ Condition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Condition

def toByte : Condition → UInt8
  | .regular => 0x41
  | .tradingHalt => 0x54
  | .wide => 0x57
  | .simpleAuction => 0x53
  | .complexAuction => 0x43
  | .simpleMarketProtection => 0x4D
  | .legMarketProtection => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Condition :=
  if byte = 0x41 then .regular
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x57 then .wide
  else if byte = 0x53 then .simpleAuction
  else if byte = 0x43 then .complexAuction
  else if byte = 0x4D then .simpleMarketProtection
  else .legMarketProtection

def ofByte (byte : UInt8) : Condition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Condition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | tradingHalt => decide
  | wide => decide
  | simpleAuction => decide
  | complexAuction => decide
  | simpleMarketProtection => decide
  | legMarketProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Condition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Condition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Condition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Condition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Condition

/-- Bid Condition: one byte code -/
def BidCondition.codes : List UInt8 :=
  [0x41, 0x54, 0x57, 0x53, 0x43, 0x4D, 0x4C]

inductive BidCondition where
  | regular -- Regular
  | tradingHalt -- Trading Halt
  | wide -- Wide
  | simpleAuction -- Simple Auction
  | complexAuction -- Complex Auction
  | simpleMarketProtection -- Simple Market Protection
  | legMarketProtection -- Leg Market Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ BidCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidCondition

def toByte : BidCondition → UInt8
  | .regular => 0x41
  | .tradingHalt => 0x54
  | .wide => 0x57
  | .simpleAuction => 0x53
  | .complexAuction => 0x43
  | .simpleMarketProtection => 0x4D
  | .legMarketProtection => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x57 then .wide
  else if byte = 0x53 then .simpleAuction
  else if byte = 0x43 then .complexAuction
  else if byte = 0x4D then .simpleMarketProtection
  else .legMarketProtection

def ofByte (byte : UInt8) : BidCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | tradingHalt => decide
  | wide => decide
  | simpleAuction => decide
  | complexAuction => decide
  | simpleMarketProtection => decide
  | legMarketProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BidCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidCondition

/-- Offer Condition: one byte code -/
def OfferCondition.codes : List UInt8 :=
  [0x41, 0x54, 0x57, 0x53, 0x43, 0x4D, 0x4C]

inductive OfferCondition where
  | regular -- Regular
  | tradingHalt -- Trading Halt
  | wide -- Wide
  | simpleAuction -- Simple Auction
  | complexAuction -- Complex Auction
  | simpleMarketProtection -- Simple Market Protection
  | legMarketProtection -- Leg Market Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferCondition

def toByte : OfferCondition → UInt8
  | .regular => 0x41
  | .tradingHalt => 0x54
  | .wide => 0x57
  | .simpleAuction => 0x53
  | .complexAuction => 0x43
  | .simpleMarketProtection => 0x4D
  | .legMarketProtection => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x57 then .wide
  else if byte = 0x53 then .simpleAuction
  else if byte = 0x43 then .complexAuction
  else if byte = 0x4D then .simpleMarketProtection
  else .legMarketProtection

def ofByte (byte : UInt8) : OfferCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | tradingHalt => decide
  | wide => decide
  | simpleAuction => decide
  | complexAuction => decide
  | simpleMarketProtection => decide
  | legMarketProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OfferCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OfferCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OfferCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OfferCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OfferCondition

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x52, 0x4F]

inductive TradingStatus where
  | halted -- Halted
  | resumed -- Resumed
  | opened -- Opened
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halted => 0x48
  | .resumed => 0x52
  | .opened => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x52 then .resumed
  else .opened

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | resumed => decide
  | opened => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Event Reason: one byte code -/
def EventReason.codes : List UInt8 :=
  [0x41, 0x4D]

inductive EventReason where
  | automatic -- Automatic
  | manual -- Manual
  | unlisted (byte : { byte : UInt8 // byte ∉ EventReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventReason

def toByte : EventReason → UInt8
  | .automatic => 0x41
  | .manual => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventReason :=
  if byte = 0x41 then .automatic
  else .manual

def ofByte (byte : UInt8) : EventReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventReason) : ofByte value.toByte = value := by
  cases value with
  | automatic => decide
  | manual => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventReason

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x53, 0x55, 0x58, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | successful -- Successful
  | invalidTradingSessionRequested -- Invalid Trading Session Requested
  | noActiveTradingSessionExists -- No Active Trading Session Exists
  | rejected -- Rejected
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .successful => 0x20
  | .invalidTradingSessionRequested => 0x53
  | .noActiveTradingSessionExists => 0x55
  | .rejected => 0x58
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x53 then .invalidTradingSessionRequested
  else if byte = 0x55 then .noActiveTradingSessionExists
  else if byte = 0x58 then .rejected
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | invalidTradingSessionRequested => decide
  | noActiveTradingSessionExists => decide
  | rejected => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badPacket -- Bad Packet
  | timedOut -- Timed Out
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badPacket => 0x42
  | .timedOut => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badPacket
  else if byte = 0x4C then .timedOut
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badPacket => decide
  | timedOut => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- Sequenced Data Packet: 10 bytes -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  matchingEngineId : BitVec 8
  sequencedMessageType : Alpha 1
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 1 message.matchingEngineId
    ++ (Alpha.encode message.sequencedMessageType))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (matchingEngineId, bytes) ← decodeUInt 1 bytes
  let (sequencedMessageType, bytes) ← Alpha.decode 1 bytes
  pure ({ sequenceNumber, matchingEngineId, sequencedMessageType }, bytes)

@[simp] theorem encode_length (message : SequencedDataPacket) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Refresh Request Message: 1 bytes -/
structure RefreshRequestMessage where
  refreshMessageType : RefreshMessageType
  deriving DecidableEq, Repr

namespace RefreshRequestMessage

def encode (message : RefreshRequestMessage) : List UInt8 :=
  RefreshMessageType.encode message.refreshMessageType

def decode (bytes : List UInt8) : Option (RefreshRequestMessage × List UInt8) := do
  let (refreshMessageType, bytes) ← RefreshMessageType.decode bytes
  pure ({ refreshMessageType }, bytes)

@[simp] theorem encode_length (message : RefreshRequestMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [RefreshMessageType.encode_length]

theorem encode_length_pos (message : RefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RefreshMessageType.decode_encode, some_bind]
  rfl

end RefreshRequestMessage

/-- System Time Message: 4 bytes -/
structure SystemTimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace SystemTimeMessage

def encode (message : SystemTimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (SystemTimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : SystemTimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SystemTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemTimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemTimeMessage

/-- Simple Series Update Message: 72 bytes -/
structure SimpleSeriesUpdateMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  underlyingSymbol : Alpha 11
  securitySymbol : Alpha 6
  expirationDate : Alpha 8
  strikePrice : BitVec 32
  callOrPut : CallOrPut
  openingTime : Alpha 8
  closingTime : Alpha 8
  restrictedOption : RestrictedOption
  longTermOption : LongTermOption
  activeOnEmerald : ActiveOnEmerald
  emeraldBboPostingIncrementIndicator : EmeraldBboPostingIncrementIndicator
  liquidityAcceptanceIncrementIndicator : LiquidityAcceptanceIncrementIndicator
  openingUnderlyingMarketCode : OpeningUnderlyingMarketCode
  priorityQuoteWidth : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SimpleSeriesUpdateMessage

def encode (message : SimpleSeriesUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.expirationDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (CallOrPut.encode message.callOrPut
    ++ (Alpha.encode message.openingTime
    ++ (Alpha.encode message.closingTime
    ++ (RestrictedOption.encode message.restrictedOption
    ++ (LongTermOption.encode message.longTermOption
    ++ (ActiveOnEmerald.encode message.activeOnEmerald
    ++ (EmeraldBboPostingIncrementIndicator.encode message.emeraldBboPostingIncrementIndicator
    ++ (LiquidityAcceptanceIncrementIndicator.encode message.liquidityAcceptanceIncrementIndicator
    ++ (OpeningUnderlyingMarketCode.encode message.openingUnderlyingMarketCode
    ++ (encodeUIntLE 4 message.priorityQuoteWidth
    ++ (Alpha.encode message.reserved8))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleSeriesUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (callOrPut, bytes) ← CallOrPut.decode bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (restrictedOption, bytes) ← RestrictedOption.decode bytes
  let (longTermOption, bytes) ← LongTermOption.decode bytes
  let (activeOnEmerald, bytes) ← ActiveOnEmerald.decode bytes
  let (emeraldBboPostingIncrementIndicator, bytes) ← EmeraldBboPostingIncrementIndicator.decode bytes
  let (liquidityAcceptanceIncrementIndicator, bytes) ← LiquidityAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (priorityQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnEmerald, emeraldBboPostingIncrementIndicator, liquidityAcceptanceIncrementIndicator, openingUnderlyingMarketCode, priorityQuoteWidth, reserved8 }, bytes)

@[simp] theorem encode_length (message : SimpleSeriesUpdateMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnEmerald.encode_length, EmeraldBboPostingIncrementIndicator.encode_length, LiquidityAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SimpleSeriesUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleSeriesUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, CallOrPut.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RestrictedOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongTermOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnEmerald.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EmeraldBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityAcceptanceIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningUnderlyingMarketCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleSeriesUpdateMessage

/-- Leg Definition: 15 bytes -/
structure LegDefinition where
  productId : BitVec 32
  legRatioQty : BitVec 16
  legSide : LegSide
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace LegDefinition

def encode (message : LegDefinition) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (LegSide.encode message.legSide
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (LegDefinition × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ productId, legRatioQty, legSide, reserved8 }, bytes)

@[simp] theorem encode_length (message : LegDefinition) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : LegDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegDefinition

/-- Complex Strategy Definition Message -/
structure ComplexStrategyDefinitionMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  underlyingSymbol : Alpha 11
  activeOnEmerald : ActiveOnEmerald
  reserved1 : Alpha 1
  updateReason : UpdateReason
  reserved10 : Alpha 10
  legDefinition : Bounded 1 LegDefinition
  deriving DecidableEq, Repr

namespace ComplexStrategyDefinitionMessage

def encode (message : ComplexStrategyDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ActiveOnEmerald.encode message.activeOnEmerald
    ++ (Alpha.encode message.reserved1
    ++ (UpdateReason.encode message.updateReason
    ++ (Alpha.encode message.reserved10
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.legDefinition.val.length)
    ++ (encodeMany LegDefinition.encode message.legDefinition.val))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDefinitionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (activeOnEmerald, bytes) ← ActiveOnEmerald.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (updateReason, bytes) ← UpdateReason.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (legDefinition_, bytes) ← decodeMany LegDefinition.decode numberOfLegs.toNat bytes
  if fits_legDefinition : legDefinition_.length < 256 ^ 1 then
    pure ({ nanoseconds, strategyId, underlyingSymbol, activeOnEmerald, reserved1, updateReason, reserved10, legDefinition := ⟨legDefinition_, fits_legDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDefinitionMessage) : (encode message).length ≤ 3858 := by
  have bound_legDefinition := message.legDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ActiveOnEmerald.encode_length, UpdateReason.encode_length, encodeMany_length_const LegDefinition.encode 15 LegDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnEmerald.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UpdateReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegDefinition.encode LegDefinition.decode LegDefinition.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legDefinition.length_lt]
  rfl

end ComplexStrategyDefinitionMessage

/-- System State Message: 17 bytes -/
structure SystemStateMessage where
  nanoseconds : BitVec 32
  cToMVersion : Alpha 8
  sessionId : BitVec 32
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.cToMVersion
    ++ (encodeUIntLE 4 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (cToMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, cToMVersion, sessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemStateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end SystemStateMessage

/-- Complex Top Of Market Best Bid Or Offer Compact Format Bid Message: 15 bytes -/
structure ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  priceShort : BitVec 16
  sizeShort : BitVec 16
  priorityCustomerSizeShort : BitVec 16
  condition : Condition
  deriving DecidableEq, Repr

namespace ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage

def encode (message : ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 2 message.priceShort
    ++ (encodeUIntLE 2 message.sizeShort
    ++ (encodeUIntLE 2 message.priorityCustomerSizeShort
    ++ (Condition.encode message.condition)))))

def decode (bytes : List UInt8) : Option (ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (priceShort, bytes) ← decodeUIntLE 2 bytes
  let (sizeShort, bytes) ← decodeUIntLE 2 bytes
  let (priorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (condition, bytes) ← Condition.decode bytes
  pure ({ nanoseconds, strategyId, priceShort, sizeShort, priorityCustomerSizeShort, condition }, bytes)

@[simp] theorem encode_length (message : ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Condition.encode_length]

theorem encode_length_pos (message : ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Condition.decode_encode, some_bind]
  rfl

end ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage

/-- Complex Top Of Market Best Bid Or Offer Compact Format Offer Message: 15 bytes -/
structure ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  priceShort : BitVec 16
  sizeShort : BitVec 16
  priorityCustomerSizeShort : BitVec 16
  condition : Condition
  deriving DecidableEq, Repr

namespace ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage

def encode (message : ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 2 message.priceShort
    ++ (encodeUIntLE 2 message.sizeShort
    ++ (encodeUIntLE 2 message.priorityCustomerSizeShort
    ++ (Condition.encode message.condition)))))

def decode (bytes : List UInt8) : Option (ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (priceShort, bytes) ← decodeUIntLE 2 bytes
  let (sizeShort, bytes) ← decodeUIntLE 2 bytes
  let (priorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (condition, bytes) ← Condition.decode bytes
  pure ({ nanoseconds, strategyId, priceShort, sizeShort, priorityCustomerSizeShort, condition }, bytes)

@[simp] theorem encode_length (message : ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Condition.encode_length]

theorem encode_length_pos (message : ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Condition.decode_encode, some_bind]
  rfl

end ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage

/-- Complex Top Of Market Best Bid Or Offer Wide Format Bid Message: 25 bytes -/
structure ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  priceLong : BitVec 64
  sizeLong : BitVec 32
  priorityCustomerSizeLong : BitVec 32
  condition : Condition
  deriving DecidableEq, Repr

namespace ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage

def encode (message : ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 8 message.priceLong
    ++ (encodeUIntLE 4 message.sizeLong
    ++ (encodeUIntLE 4 message.priorityCustomerSizeLong
    ++ (Condition.encode message.condition)))))

def decode (bytes : List UInt8) : Option (ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (priceLong, bytes) ← decodeUIntLE 8 bytes
  let (sizeLong, bytes) ← decodeUIntLE 4 bytes
  let (priorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (condition, bytes) ← Condition.decode bytes
  pure ({ nanoseconds, strategyId, priceLong, sizeLong, priorityCustomerSizeLong, condition }, bytes)

@[simp] theorem encode_length (message : ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Condition.encode_length]

theorem encode_length_pos (message : ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Condition.decode_encode, some_bind]
  rfl

end ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage

/-- Complex Top Of Market Best Bid Or Offer Wide Format Offer Message: 25 bytes -/
structure ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  priceLong : BitVec 64
  sizeLong : BitVec 32
  priorityCustomerSizeLong : BitVec 32
  condition : Condition
  deriving DecidableEq, Repr

namespace ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage

def encode (message : ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 8 message.priceLong
    ++ (encodeUIntLE 4 message.sizeLong
    ++ (encodeUIntLE 4 message.priorityCustomerSizeLong
    ++ (Condition.encode message.condition)))))

def decode (bytes : List UInt8) : Option (ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (priceLong, bytes) ← decodeUIntLE 8 bytes
  let (sizeLong, bytes) ← decodeUIntLE 4 bytes
  let (priorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (condition, bytes) ← Condition.decode bytes
  pure ({ nanoseconds, strategyId, priceLong, sizeLong, priorityCustomerSizeLong, condition }, bytes)

@[simp] theorem encode_length (message : ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Condition.encode_length]

theorem encode_length_pos (message : ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Condition.decode_encode, some_bind]
  rfl

end ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage

/-- Complex Double Sided Top Of Market Best Bid And Offer Compact Format Message: 22 bytes -/
structure ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  bidPriorityCustomerSizeShort : BitVec 16
  bidCondition : BidCondition
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  offerPriorityCustomerSizeShort : BitVec 16
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage

def encode (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 2 message.bidPriceShort
    ++ (encodeUIntLE 2 message.bidSizeShort
    ++ (encodeUIntLE 2 message.bidPriorityCustomerSizeShort
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 2 message.offerPriceShort
    ++ (encodeUIntLE 2 message.offerSizeShort
    ++ (encodeUIntLE 2 message.offerPriorityCustomerSizeShort
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (bidSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (bidPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (offerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (offerPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, strategyId, bidPriceShort, bidSizeShort, bidPriorityCustomerSizeShort, bidCondition, offerPriceShort, offerSizeShort, offerPriorityCustomerSizeShort, offerCondition }, bytes)

@[simp] theorem encode_length (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, BidCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage

/-- Complex Double Sided Top Of Market Best Bid And Offer Wide Format Message: 42 bytes -/
structure ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  bidPriceLong : BitVec 64
  bidSizeLong : BitVec 32
  bidPriorityCustomerSizeLong : BitVec 32
  bidCondition : BidCondition
  offerPriceLong : BitVec 64
  offerSizeLong : BitVec 32
  offerPriorityCustomerSizeLong : BitVec 32
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage

def encode (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 8 message.bidPriceLong
    ++ (encodeUIntLE 4 message.bidSizeLong
    ++ (encodeUIntLE 4 message.bidPriorityCustomerSizeLong
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 8 message.offerPriceLong
    ++ (encodeUIntLE 4 message.offerSizeLong
    ++ (encodeUIntLE 4 message.offerPriorityCustomerSizeLong
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceLong, bytes) ← decodeUIntLE 8 bytes
  let (bidSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (bidPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPriceLong, bytes) ← decodeUIntLE 8 bytes
  let (offerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (offerPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, strategyId, bidPriceLong, bidSizeLong, bidPriorityCustomerSizeLong, bidCondition, offerPriceLong, offerSizeLong, offerPriorityCustomerSizeLong, offerCondition }, bytes)

@[simp] theorem encode_length (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, BidCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage

/-- Strategy Last Sale Message: 41 bytes -/
structure StrategyLastSaleMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  tradeId : BitVec 32
  netPrice : BitVec 64
  sizeLong : BitVec 32
  condition : Condition
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace StrategyLastSaleMessage

def encode (message : StrategyLastSaleMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.netPrice
    ++ (encodeUIntLE 4 message.sizeLong
    ++ (Condition.encode message.condition
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (StrategyLastSaleMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (netPrice, bytes) ← decodeUIntLE 8 bytes
  let (sizeLong, bytes) ← decodeUIntLE 4 bytes
  let (condition, bytes) ← Condition.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ nanoseconds, strategyId, tradeId, netPrice, sizeLong, condition, reserved16 }, bytes)

@[simp] theorem encode_length (message : StrategyLastSaleMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Condition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyLastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyLastSaleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Condition.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyLastSaleMessage

/-- Underlying Trading Status Notification Message: 25 bytes -/
structure UnderlyingTradingStatusNotificationMessage where
  nanoseconds : BitVec 32
  underlyingSymbol : Alpha 11
  tradingStatus : TradingStatus
  eventReason : EventReason
  expectedEventTimeSecondsPart : BitVec 32
  expectedEventTimeNanoSecondsPart : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusNotificationMessage

def encode (message : UnderlyingTradingStatusNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 4 message.expectedEventTimeSecondsPart
    ++ (encodeUIntLE 4 message.expectedEventTimeNanoSecondsPart)))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (expectedEventTimeSecondsPart, bytes) ← decodeUIntLE 4 bytes
  let (expectedEventTimeNanoSecondsPart, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, underlyingSymbol, tradingStatus, eventReason, expectedEventTimeSecondsPart, expectedEventTimeNanoSecondsPart }, bytes)

@[simp] theorem encode_length (message : UnderlyingTradingStatusNotificationMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length, EventReason.encode_length]

theorem encode_length_pos (message : UnderlyingTradingStatusNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingTradingStatusNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end UnderlyingTradingStatusNotificationMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | simpleSeriesUpdateMessage (message : SimpleSeriesUpdateMessage) -- "P" 0x50
  | complexStrategyDefinitionMessage (message : ComplexStrategyDefinitionMessage) -- "C" 0x43
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | complexTopOfMarketBestBidOrOfferCompactFormatBidMessage (message : ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage) -- "b" 0x62
  | complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage (message : ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage) -- "o" 0x6F
  | complexTopOfMarketBestBidOrOfferWideFormatBidMessage (message : ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage) -- "e" 0x65
  | complexTopOfMarketBestBidOrOfferWideFormatOfferMessage (message : ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage) -- "f" 0x66
  | complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage) -- "m" 0x6D
  | complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage (message : ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage) -- "w" 0x77
  | strategyLastSaleMessage (message : StrategyLastSaleMessage) -- "t" 0x74
  | underlyingTradingStatusNotificationMessage (message : UnderlyingTradingStatusNotificationMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .simpleSeriesUpdateMessage _ => 80
  | .complexStrategyDefinitionMessage _ => 67
  | .systemStateMessage _ => 83
  | .complexTopOfMarketBestBidOrOfferCompactFormatBidMessage _ => 98
  | .complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage _ => 111
  | .complexTopOfMarketBestBidOrOfferWideFormatBidMessage _ => 101
  | .complexTopOfMarketBestBidOrOfferWideFormatOfferMessage _ => 102
  | .complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage _ => 109
  | .complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage _ => 119
  | .strategyLastSaleMessage _ => 116
  | .underlyingTradingStatusNotificationMessage _ => 72

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .simpleSeriesUpdateMessage message => SimpleSeriesUpdateMessage.encode message
  | .complexStrategyDefinitionMessage message => ComplexStrategyDefinitionMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .complexTopOfMarketBestBidOrOfferCompactFormatBidMessage message => ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.encode message
  | .complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage message => ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode message
  | .complexTopOfMarketBestBidOrOfferWideFormatBidMessage message => ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.encode message
  | .complexTopOfMarketBestBidOrOfferWideFormatOfferMessage message => ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.encode message
  | .complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage message => ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.encode message
  | .complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage message => ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.encode message
  | .strategyLastSaleMessage message => StrategyLastSaleMessage.encode message
  | .underlyingTradingStatusNotificationMessage message => UnderlyingTradingStatusNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 3858 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | simpleSeriesUpdateMessage inner =>
    simp only [encode, SimpleSeriesUpdateMessage.encode_length]
    omega
  | complexStrategyDefinitionMessage inner =>
    have bound_inner := ComplexStrategyDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferCompactFormatBidMessage inner =>
    simp only [encode, ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage inner =>
    simp only [encode, ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferWideFormatBidMessage inner =>
    simp only [encode, ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferWideFormatOfferMessage inner =>
    simp only [encode, ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.encode_length]
    omega
  | complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage inner =>
    simp only [encode, ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.encode_length]
    omega
  | complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage inner =>
    simp only [encode, ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.encode_length]
    omega
  | strategyLastSaleMessage inner =>
    simp only [encode, StrategyLastSaleMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [encode, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 80 then (SimpleSeriesUpdateMessage.decode bytes).map fun (message, rest) => (.simpleSeriesUpdateMessage message, rest)
  else if tag = 67 then (ComplexStrategyDefinitionMessage.decode bytes).map fun (message, rest) => (.complexStrategyDefinitionMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 98 then (ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.decode bytes).map fun (message, rest) => (.complexTopOfMarketBestBidOrOfferCompactFormatBidMessage message, rest)
  else if tag = 111 then (ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.decode bytes).map fun (message, rest) => (.complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage message, rest)
  else if tag = 101 then (ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.decode bytes).map fun (message, rest) => (.complexTopOfMarketBestBidOrOfferWideFormatBidMessage message, rest)
  else if tag = 102 then (ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.decode bytes).map fun (message, rest) => (.complexTopOfMarketBestBidOrOfferWideFormatOfferMessage message, rest)
  else if tag = 109 then (ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.decode bytes).map fun (message, rest) => (.complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage message, rest)
  else if tag = 119 then (ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.decode bytes).map fun (message, rest) => (.complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage message, rest)
  else if tag = 116 then (StrategyLastSaleMessage.decode bytes).map fun (message, rest) => (.strategyLastSaleMessage message, rest)
  else if tag = 72 then (UnderlyingTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Application Message -/
structure ApplicationMessage where
  data : Data
  deriving DecidableEq, Repr

namespace ApplicationMessage

def encode (message : ApplicationMessage) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (Data.encode message.data)

def decode (bytes : List UInt8) : Option (ApplicationMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ data }, bytes)

theorem encode_length_pos (message : ApplicationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 3859 := by
  unfold encode
  cases message.data with
  | systemTimeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemTimeMessage.encode_length]
    omega
  | simpleSeriesUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleSeriesUpdateMessage.encode_length]
    omega
  | complexStrategyDefinitionMessage inner =>
    have bound_inner := ComplexStrategyDefinitionMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, encodeUInt_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferCompactFormatBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferCompactFormatOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferWideFormatBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.encode_length]
    omega
  | complexTopOfMarketBestBidOrOfferWideFormatOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.encode_length]
    omega
  | complexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.encode_length]
    omega
  | complexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.encode_length]
    omega
  | strategyLastSaleMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, StrategyLastSaleMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

/-- Refresh Response Message -/
structure RefreshResponseMessage where
  sequenceNumber : BitVec 64
  applicationMessage : ApplicationMessage
  deriving DecidableEq, Repr

namespace RefreshResponseMessage

def encode (message : RefreshResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (ApplicationMessage.encode message.applicationMessage)

def decode (bytes : List UInt8) : Option (RefreshResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (applicationMessage, bytes) ← ApplicationMessage.decode bytes
  pure ({ sequenceNumber, applicationMessage }, bytes)

theorem encode_length_pos (message : RefreshResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : RefreshResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ApplicationMessage.decode_encode, some_bind]
  rfl

end RefreshResponseMessage

/-- End Of Refresh Notification Message: 1 bytes -/
structure EndOfRefreshNotificationMessage where
  refreshMessageType : RefreshMessageType
  deriving DecidableEq, Repr

namespace EndOfRefreshNotificationMessage

def encode (message : EndOfRefreshNotificationMessage) : List UInt8 :=
  RefreshMessageType.encode message.refreshMessageType

def decode (bytes : List UInt8) : Option (EndOfRefreshNotificationMessage × List UInt8) := do
  let (refreshMessageType, bytes) ← RefreshMessageType.decode bytes
  pure ({ refreshMessageType }, bytes)

@[simp] theorem encode_length (message : EndOfRefreshNotificationMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [RefreshMessageType.encode_length]

theorem encode_length_pos (message : EndOfRefreshNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfRefreshNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RefreshMessageType.decode_encode, some_bind]
  rfl

end EndOfRefreshNotificationMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | refreshRequestMessage (message : RefreshRequestMessage) -- "R" 0x52
  | refreshResponseMessage (message : RefreshResponseMessage) -- "r" 0x72
  | endOfRefreshNotificationMessage (message : EndOfRefreshNotificationMessage) -- "E" 0x45
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .refreshRequestMessage _ => 82
  | .refreshResponseMessage _ => 114
  | .endOfRefreshNotificationMessage _ => 69

def encode : UnsequencedMessage → List UInt8
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .refreshResponseMessage message => RefreshResponseMessage.encode message
  | .endOfRefreshNotificationMessage message => EndOfRefreshNotificationMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 82 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 114 then (RefreshResponseMessage.decode bytes).map fun (message, rest) => (.refreshResponseMessage message, rest)
  else if tag = 69 then (EndOfRefreshNotificationMessage.decode bytes).map fun (message, rest) => (.endOfRefreshNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedTradingSessionId : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedTradingSessionId
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedTradingSessionId, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedTradingSessionId, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 11 bytes -/
structure LoginResponse where
  numberOfMatchingEngines : BitVec 8
  loginStatus : LoginStatus
  tradingSessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  encodeUInt 1 message.numberOfMatchingEngines
    ++ (LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUInt 1 bytes
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ numberOfMatchingEngines, loginStatus, tradingSessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LoginStatus.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 1 bytes -/
structure SynchronizationComplete where
  numberOfMatchingEngines : BitVec 8
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (message : SynchronizationComplete) : List UInt8 :=
  encodeUInt 1 message.numberOfMatchingEngines

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUInt 1 bytes
  pure ({ numberOfMatchingEngines }, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SynchronizationComplete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 61666
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61666 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 61667 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  logoutReason : LogoutReason
  logoutText : Capped 61666
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61666 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 61667 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

/-- Trading Session Update: 0 bytes -/
structure TradingSessionUpdate where
  deriving DecidableEq, Repr

namespace TradingSessionUpdate

def encode (_ : TradingSessionUpdate) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TradingSessionUpdate × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TradingSessionUpdate) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradingSessionUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionUpdate) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingSessionUpdate

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

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Test Packet -/
structure TestPacket where
  testText : Capped 61666
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 61666 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 61666 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "s" 0x73
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "l" 0x6C
  | loginResponse (message : LoginResponse) -- "r" 0x72
  | synchronizationComplete (message : SynchronizationComplete) -- "c" 0x63
  | retransmissionRequest (message : RetransmissionRequest) -- "a" 0x61
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | tradingSessionUpdate (message : TradingSessionUpdate) -- "u" 0x75
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  | testPacket (message : TestPacket) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 115
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 108
  | .loginResponse _ => 114
  | .synchronizationComplete _ => 99
  | .retransmissionRequest _ => 97
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .tradingSessionUpdate _ => 117
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49
  | .testPacket _ => 84

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .tradingSessionUpdate message => TradingSessionUpdate.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .testPacket message => TestPacket.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 115 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 108 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 114 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 99 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 97 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 117 then (TradingSessionUpdate.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionUpdate message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 84 then (TestPacket.decode bytes).map fun message => .testPacket message
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | tradingSessionUpdate message => simp [decode, encode, tag, TradingSessionUpdate.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | testPacket message => simp [decode, encode, tag, TestPacket.decode_encode]

end SesmPayload

/-- Sesm Tcp Packet: the body, which the record carries with the proof it fits its frame -/
structure SesmTcpPacketBody where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacketBody

def encodeBody (message : SesmTcpPacketBody) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacketBody := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

end SesmTcpPacketBody

/-- Sesm Tcp Packet: the body with the proof its encoding fits Sesm Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev SesmTcpPacket := Fitting SesmTcpPacketBody.encodeBody 0 65536

namespace SesmTcpPacket

def encode (message : SesmTcpPacket) : List UInt8 :=
  encodeFramedLE 2 0 SesmTcpPacketBody.encodeBody message.val

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFittingAllLE 2 0 SesmTcpPacketBody.encodeBody SesmTcpPacketBody.decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 0 SesmTcpPacketBody.encodeBody SesmTcpPacketBody.decodeBody message (SesmTcpPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : SesmTcpPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SesmTcpPacket

/-- Tcp Packet -/
structure TcpPacket where
  sesmTcpPacket : List SesmTcpPacket
  deriving DecidableEq, Repr

namespace TcpPacket

def encode (message : TcpPacket) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option TcpPacket := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  pure { sesmTcpPacket }

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rfl

end TcpPacket

end Omi.MiaxEmeraldoptionsComplextopofmarketMachV10ATcp
