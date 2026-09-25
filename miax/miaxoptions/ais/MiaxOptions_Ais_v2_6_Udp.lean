import Omi.Wire

/-!
# Miami International Holdings Administrative Information Subscriber v2.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Udp Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxMiaxoptionsAisMachV26Udp

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

/-- Active On Miax: one byte code -/
def ActiveOnMiax.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnMiax where
  | active -- Active
  | inactive -- Inactive
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnMiax.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnMiax

def toByte : ActiveOnMiax → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnMiax :=
  if byte = 0x41 then .active
  else .inactive

def ofByte (byte : UInt8) : ActiveOnMiax :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnMiax) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnMiax) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnMiax × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnMiax) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ActiveOnMiax) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnMiax

/-- Miax Bbo Posting Increment Indicator: one byte code -/
def MiaxBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive MiaxBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MiaxBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MiaxBboPostingIncrementIndicator

def toByte : MiaxBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MiaxBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MiaxBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MiaxBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MiaxBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MiaxBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MiaxBboPostingIncrementIndicator

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
  | nasdaqOmxUtp -- Nasdaq Omx Utp
  | nasdaqOmxCta -- Nasdaq Omx Cta
  | memx -- Memx
  | iex -- Iex
  | cboeStockExchange -- Cboe Stock Exchange
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
  | .nasdaqOmxUtp => 0x51
  | .nasdaqOmxCta => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cboeStockExchange => 0x57
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
  else if byte = 0x51 then .nasdaqOmxUtp
  else if byte = 0x54 then .nasdaqOmxCta
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cboeStockExchange
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
  | nasdaqOmxUtp => decide
  | nasdaqOmxCta => decide
  | memx => decide
  | iex => decide
  | cboeStockExchange => decide
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
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startOfTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startOfTestSession => decide
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

/-- Event Type: one byte code -/
def EventType.codes : List UInt8 :=
  [0x4C, 0x4F, 0x52, 0x50, 0x53, 0x45, 0x43]

inductive EventType where
  | liquidityRefreshMechanism -- Liquidity Refresh Mechanism
  | openingReopeningImbalanceMechanism -- Opening Reopening Imbalance Mechanism
  | routeMechanism -- Route Mechanism
  | miaxPrimePairedOrder -- Miax Prime Paired Order
  | settlementOpeningImbalanceMechanism -- Settlement Opening Imbalance Mechanism
  | liquidityExposureProcess -- Liquidity Exposure Process
  | complexOrderAuction -- Complex Order Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ EventType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventType

def toByte : EventType → UInt8
  | .liquidityRefreshMechanism => 0x4C
  | .openingReopeningImbalanceMechanism => 0x4F
  | .routeMechanism => 0x52
  | .miaxPrimePairedOrder => 0x50
  | .settlementOpeningImbalanceMechanism => 0x53
  | .liquidityExposureProcess => 0x45
  | .complexOrderAuction => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventType :=
  if byte = 0x4C then .liquidityRefreshMechanism
  else if byte = 0x4F then .openingReopeningImbalanceMechanism
  else if byte = 0x52 then .routeMechanism
  else if byte = 0x50 then .miaxPrimePairedOrder
  else if byte = 0x53 then .settlementOpeningImbalanceMechanism
  else if byte = 0x45 then .liquidityExposureProcess
  else .complexOrderAuction

def ofByte (byte : UInt8) : EventType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventType) : ofByte value.toByte = value := by
  cases value with
  | liquidityRefreshMechanism => decide
  | openingReopeningImbalanceMechanism => decide
  | routeMechanism => decide
  | miaxPrimePairedOrder => decide
  | settlementOpeningImbalanceMechanism => decide
  | liquidityExposureProcess => decide
  | complexOrderAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventType

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive ImbalanceSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x20]

inductive Origin where
  | marketMaker -- Market Maker
  | awayMarketMaker -- Away Market Maker
  | brokerDealer -- Broker Dealer
  | firm -- Firm
  | priorityCustomer -- Priority Customer
  | nonPriorityCustomer -- Non Priority Customer
  | multipleInitiatorsOfVaryingOrigin -- Multiple Initiators Of Varying Origin
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .marketMaker => 0x31
  | .awayMarketMaker => 0x32
  | .brokerDealer => 0x33
  | .firm => 0x34
  | .priorityCustomer => 0x35
  | .nonPriorityCustomer => 0x36
  | .multipleInitiatorsOfVaryingOrigin => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x31 then .marketMaker
  else if byte = 0x32 then .awayMarketMaker
  else if byte = 0x33 then .brokerDealer
  else if byte = 0x34 then .firm
  else if byte = 0x35 then .priorityCustomer
  else if byte = 0x36 then .nonPriorityCustomer
  else .multipleInitiatorsOfVaryingOrigin

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | marketMaker => decide
  | awayMarketMaker => decide
  | brokerDealer => decide
  | firm => decide
  | priorityCustomer => decide
  | nonPriorityCustomer => decide
  | multipleInitiatorsOfVaryingOrigin => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Origin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Origin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Origin) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Origin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Origin

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x41]

inductive Side where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
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

/-- Option State: one byte code -/
def OptionState.codes : List UInt8 :=
  [0x50, 0x4E, 0x4F]

inductive OptionState where
  | preOpen -- Pre Open
  | openButNoFsrp -- Open But No Fsrp
  | openWithFsrp -- Open With Fsrp
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionState

def toByte : OptionState → UInt8
  | .preOpen => 0x50
  | .openButNoFsrp => 0x4E
  | .openWithFsrp => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionState :=
  if byte = 0x50 then .preOpen
  else if byte = 0x4E then .openButNoFsrp
  else .openWithFsrp

def ofByte (byte : UInt8) : OptionState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionState) : ofByte value.toByte = value := by
  cases value with
  | preOpen => decide
  | openButNoFsrp => decide
  | openWithFsrp => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionState

/-- Settlement Reference Price Type: one byte code -/
def SettlementReferencePriceType.codes : List UInt8 :=
  [0x45, 0x41, 0x4F, 0x53]

inductive SettlementReferencePriceType where
  | expectedOpeningPrice -- Expected Opening Price
  | auctionOnlyPrice -- Auction Only Price
  | openingPrice -- Opening Price
  | finalSettlementReferencePrice -- Final Settlement Reference Price
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementReferencePriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementReferencePriceType

def toByte : SettlementReferencePriceType → UInt8
  | .expectedOpeningPrice => 0x45
  | .auctionOnlyPrice => 0x41
  | .openingPrice => 0x4F
  | .finalSettlementReferencePrice => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementReferencePriceType :=
  if byte = 0x45 then .expectedOpeningPrice
  else if byte = 0x41 then .auctionOnlyPrice
  else if byte = 0x4F then .openingPrice
  else .finalSettlementReferencePrice

def ofByte (byte : UInt8) : SettlementReferencePriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementReferencePriceType) : ofByte value.toByte = value := by
  cases value with
  | expectedOpeningPrice => decide
  | auctionOnlyPrice => decide
  | openingPrice => decide
  | finalSettlementReferencePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementReferencePriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementReferencePriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementReferencePriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementReferencePriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementReferencePriceType

/-- Opening Condition: one byte code -/
def OpeningCondition.codes : List UInt8 :=
  [0x51, 0x43, 0x41, 0x42, 0x53, 0x4F, 0x4E, 0x52]

inductive OpeningCondition where
  | needQuote -- Need Quote
  | crossedQuote -- Crossed Quote
  | crossedAwayQuote -- Crossed Away Quote
  | needBuyers -- Need Buyers
  | needSellers -- Need Sellers
  | wouldOpen -- Would Open
  | openWithNoFinalSrp -- Open With No Final Srp
  | openWithFinalSrp -- Open With Final Srp
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningCondition

def toByte : OpeningCondition → UInt8
  | .needQuote => 0x51
  | .crossedQuote => 0x43
  | .crossedAwayQuote => 0x41
  | .needBuyers => 0x42
  | .needSellers => 0x53
  | .wouldOpen => 0x4F
  | .openWithNoFinalSrp => 0x4E
  | .openWithFinalSrp => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningCondition :=
  if byte = 0x51 then .needQuote
  else if byte = 0x43 then .crossedQuote
  else if byte = 0x41 then .crossedAwayQuote
  else if byte = 0x42 then .needBuyers
  else if byte = 0x53 then .needSellers
  else if byte = 0x4F then .wouldOpen
  else if byte = 0x4E then .openWithNoFinalSrp
  else .openWithFinalSrp

def ofByte (byte : UInt8) : OpeningCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningCondition) : ofByte value.toByte = value := by
  cases value with
  | needQuote => decide
  | crossedQuote => decide
  | crossedAwayQuote => decide
  | needBuyers => decide
  | needSellers => decide
  | wouldOpen => decide
  | openWithNoFinalSrp => decide
  | openWithFinalSrp => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningCondition

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

/-- Start Of Session: 0 bytes -/
structure StartOfSession where
  deriving DecidableEq, Repr

namespace StartOfSession

def encode (_ : StartOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfSession

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
  activeOnMiax : ActiveOnMiax
  miaxBboPostingIncrementIndicator : MiaxBboPostingIncrementIndicator
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
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (MiaxBboPostingIncrementIndicator.encode message.miaxBboPostingIncrementIndicator
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
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (miaxBboPostingIncrementIndicator, bytes) ← MiaxBboPostingIncrementIndicator.decode bytes
  let (liquidityAcceptanceIncrementIndicator, bytes) ← LiquidityAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (priorityQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnMiax, miaxBboPostingIncrementIndicator, liquidityAcceptanceIncrementIndicator, openingUnderlyingMarketCode, priorityQuoteWidth, reserved8 }, bytes)

@[simp] theorem encode_length (message : SimpleSeriesUpdateMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnMiax.encode_length, MiaxBboPostingIncrementIndicator.encode_length, LiquidityAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

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
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MiaxBboPostingIncrementIndicator.decode_encode, some_bind]
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

/-- Complex Strategy Definition Update Message -/
structure ComplexStrategyDefinitionUpdateMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  underlyingSymbol : Alpha 11
  activeOnMiax : ActiveOnMiax
  reserved1 : Alpha 1
  updateReason : UpdateReason
  reserved10 : Alpha 10
  legDefinition : Bounded 1 LegDefinition
  deriving DecidableEq, Repr

namespace ComplexStrategyDefinitionUpdateMessage

def encode (message : ComplexStrategyDefinitionUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (Alpha.encode message.reserved1
    ++ (UpdateReason.encode message.updateReason
    ++ (Alpha.encode message.reserved10
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.legDefinition.val.length)
    ++ (encodeMany LegDefinition.encode message.legDefinition.val))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDefinitionUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (updateReason, bytes) ← UpdateReason.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (legDefinition_, bytes) ← decodeMany LegDefinition.decode numberOfLegs.toNat bytes
  if fits_legDefinition : legDefinition_.length < 256 ^ 1 then
    pure ({ nanoseconds, strategyId, underlyingSymbol, activeOnMiax, reserved1, updateReason, reserved10, legDefinition := ⟨legDefinition_, fits_legDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDefinitionUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDefinitionUpdateMessage) : (encode message).length ≤ 3858 := by
  have bound_legDefinition := message.legDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ActiveOnMiax.encode_length, UpdateReason.encode_length, encodeMany_length_const LegDefinition.encode 15 LegDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDefinitionUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
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

end ComplexStrategyDefinitionUpdateMessage

/-- System State Message: 17 bytes -/
structure SystemStateMessage where
  nanoseconds : BitVec 32
  aisVersion : Alpha 8
  sessionId : BitVec 32
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.aisVersion
    ++ (encodeUIntLE 4 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (aisVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, aisVersion, sessionId, systemStatus }, bytes)

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

/-- Simple Liquidity Seeking Event Notification Message: 46 bytes -/
structure SimpleLiquiditySeekingEventNotificationMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  eventType : EventType
  eventId : BitVec 32
  priceShort : BitVec 32
  imbalanceSide : ImbalanceSide
  quantity1 : BitVec 32
  quantity2 : BitVec 32
  quantity3 : BitVec 32
  quantity4 : BitVec 32
  attributableId : Alpha 4
  origin : Origin
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace SimpleLiquiditySeekingEventNotificationMessage

def encode (message : SimpleLiquiditySeekingEventNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (EventType.encode message.eventType
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.priceShort
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.quantity1
    ++ (encodeUIntLE 4 message.quantity2
    ++ (encodeUIntLE 4 message.quantity3
    ++ (encodeUIntLE 4 message.quantity4
    ++ (Alpha.encode message.attributableId
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.reserved7))))))))))))

def decode (bytes : List UInt8) : Option (SimpleLiquiditySeekingEventNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← EventType.decode bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (priceShort, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (quantity1, bytes) ← decodeUIntLE 4 bytes
  let (quantity2, bytes) ← decodeUIntLE 4 bytes
  let (quantity3, bytes) ← decodeUIntLE 4 bytes
  let (quantity4, bytes) ← decodeUIntLE 4 bytes
  let (attributableId, bytes) ← Alpha.decode 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, productId, eventType, eventId, priceShort, imbalanceSide, quantity1, quantity2, quantity3, quantity4, attributableId, origin, reserved7 }, bytes)

@[simp] theorem encode_length (message : SimpleLiquiditySeekingEventNotificationMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventType.encode_length, ImbalanceSide.encode_length, Alpha.encode_length, Origin.encode_length]

theorem encode_length_pos (message : SimpleLiquiditySeekingEventNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleLiquiditySeekingEventNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleLiquiditySeekingEventNotificationMessage

/-- Complex Liquidity Seeking Event Notification Message: 42 bytes -/
structure ComplexLiquiditySeekingEventNotificationMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  eventType : EventType
  eventId : BitVec 32
  side : Side
  priceLong : BitVec 64
  matchedQuantity : BitVec 32
  imbalanceQuantitySigned : BitVec 32
  attributableId : Alpha 4
  origin : Origin
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace ComplexLiquiditySeekingEventNotificationMessage

def encode (message : ComplexLiquiditySeekingEventNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (EventType.encode message.eventType
    ++ (encodeUIntLE 4 message.eventId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.priceLong
    ++ (encodeUIntLE 4 message.matchedQuantity
    ++ (encodeUIntLE 4 message.imbalanceQuantitySigned
    ++ (Alpha.encode message.attributableId
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.reserved7))))))))))

def decode (bytes : List UInt8) : Option (ComplexLiquiditySeekingEventNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← EventType.decode bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (priceLong, bytes) ← decodeUIntLE 8 bytes
  let (matchedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceQuantitySigned, bytes) ← decodeUIntLE 4 bytes
  let (attributableId, bytes) ← Alpha.decode 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, strategyId, eventType, eventId, side, priceLong, matchedQuantity, imbalanceQuantitySigned, attributableId, origin, reserved7 }, bytes)

@[simp] theorem encode_length (message : ComplexLiquiditySeekingEventNotificationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventType.encode_length, Side.encode_length, Alpha.encode_length, Origin.encode_length]

theorem encode_length_pos (message : ComplexLiquiditySeekingEventNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexLiquiditySeekingEventNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexLiquiditySeekingEventNotificationMessage

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

/-- Theoretical Settlement Reference Price Notification Message: 110 bytes -/
structure TheoreticalSettlementReferencePriceNotificationMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  underlyingSymbol : Alpha 11
  securitySymbol : Alpha 6
  expirationDate : Alpha 8
  strikePrice : BitVec 32
  callOrPut : CallOrPut
  optionState : OptionState
  priorDayReferencePrice : BitVec 32
  settlementReferencePrice : BitVec 32
  settlementReferencePriceType : SettlementReferencePriceType
  saoBuyQuantity1 : BitVec 32
  saoSellQuantity1 : BitVec 32
  saoBuyQuantity2 : BitVec 32
  saoSellQuantity2 : BitVec 32
  nonSaoBuyQuantity : BitVec 32
  nonSaoSellQuantity : BitVec 32
  totalBuyQuantity : BitVec 32
  totalSellQuantity : BitVec 32
  imbalanceSide : ImbalanceSide
  imbalanceQuantityUnsigned : BitVec 32
  mustFillQuantity : BitVec 32
  matchedQuantity : BitVec 32
  openingCondition : OpeningCondition
  mbb : BitVec 32
  mbo : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace TheoreticalSettlementReferencePriceNotificationMessage

def encode (message : TheoreticalSettlementReferencePriceNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.expirationDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (CallOrPut.encode message.callOrPut
    ++ (OptionState.encode message.optionState
    ++ (encodeUIntLE 4 message.priorDayReferencePrice
    ++ (encodeUIntLE 4 message.settlementReferencePrice
    ++ (SettlementReferencePriceType.encode message.settlementReferencePriceType
    ++ (encodeUIntLE 4 message.saoBuyQuantity1
    ++ (encodeUIntLE 4 message.saoSellQuantity1
    ++ (encodeUIntLE 4 message.saoBuyQuantity2
    ++ (encodeUIntLE 4 message.saoSellQuantity2
    ++ (encodeUIntLE 4 message.nonSaoBuyQuantity
    ++ (encodeUIntLE 4 message.nonSaoSellQuantity
    ++ (encodeUIntLE 4 message.totalBuyQuantity
    ++ (encodeUIntLE 4 message.totalSellQuantity
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.imbalanceQuantityUnsigned
    ++ (encodeUIntLE 4 message.mustFillQuantity
    ++ (encodeUIntLE 4 message.matchedQuantity
    ++ (OpeningCondition.encode message.openingCondition
    ++ (encodeUIntLE 4 message.mbb
    ++ (encodeUIntLE 4 message.mbo
    ++ (Alpha.encode message.reserved8))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TheoreticalSettlementReferencePriceNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (callOrPut, bytes) ← CallOrPut.decode bytes
  let (optionState, bytes) ← OptionState.decode bytes
  let (priorDayReferencePrice, bytes) ← decodeUIntLE 4 bytes
  let (settlementReferencePrice, bytes) ← decodeUIntLE 4 bytes
  let (settlementReferencePriceType, bytes) ← SettlementReferencePriceType.decode bytes
  let (saoBuyQuantity1, bytes) ← decodeUIntLE 4 bytes
  let (saoSellQuantity1, bytes) ← decodeUIntLE 4 bytes
  let (saoBuyQuantity2, bytes) ← decodeUIntLE 4 bytes
  let (saoSellQuantity2, bytes) ← decodeUIntLE 4 bytes
  let (nonSaoBuyQuantity, bytes) ← decodeUIntLE 4 bytes
  let (nonSaoSellQuantity, bytes) ← decodeUIntLE 4 bytes
  let (totalBuyQuantity, bytes) ← decodeUIntLE 4 bytes
  let (totalSellQuantity, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (imbalanceQuantityUnsigned, bytes) ← decodeUIntLE 4 bytes
  let (mustFillQuantity, bytes) ← decodeUIntLE 4 bytes
  let (matchedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (openingCondition, bytes) ← OpeningCondition.decode bytes
  let (mbb, bytes) ← decodeUIntLE 4 bytes
  let (mbo, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, optionState, priorDayReferencePrice, settlementReferencePrice, settlementReferencePriceType, saoBuyQuantity1, saoSellQuantity1, saoBuyQuantity2, saoSellQuantity2, nonSaoBuyQuantity, nonSaoSellQuantity, totalBuyQuantity, totalSellQuantity, imbalanceSide, imbalanceQuantityUnsigned, mustFillQuantity, matchedQuantity, openingCondition, mbb, mbo, reserved8 }, bytes)

@[simp] theorem encode_length (message : TheoreticalSettlementReferencePriceNotificationMessage) : (encode message).length = 110 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, OptionState.encode_length, SettlementReferencePriceType.encode_length, ImbalanceSide.encode_length, OpeningCondition.encode_length]

theorem encode_length_pos (message : TheoreticalSettlementReferencePriceNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TheoreticalSettlementReferencePriceNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OptionState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementReferencePriceType.decode_encode, some_bind]
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
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TheoreticalSettlementReferencePriceNotificationMessage

/-- Theoretical Settlement Price Notification Message: 32 bytes -/
structure TheoreticalSettlementPriceNotificationMessage where
  nanoseconds : BitVec 32
  settlementSymbol : Alpha 8
  theoreticalSettlementPrice : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace TheoreticalSettlementPriceNotificationMessage

def encode (message : TheoreticalSettlementPriceNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.settlementSymbol
    ++ (encodeUIntLE 4 message.theoreticalSettlementPrice
    ++ (Alpha.encode message.reserved16)))

def decode (bytes : List UInt8) : Option (TheoreticalSettlementPriceNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (settlementSymbol, bytes) ← Alpha.decode 8 bytes
  let (theoreticalSettlementPrice, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ nanoseconds, settlementSymbol, theoreticalSettlementPrice, reserved16 }, bytes)

@[simp] theorem encode_length (message : TheoreticalSettlementPriceNotificationMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TheoreticalSettlementPriceNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TheoreticalSettlementPriceNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TheoreticalSettlementPriceNotificationMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | simpleSeriesUpdateMessage (message : SimpleSeriesUpdateMessage) -- "P" 0x50
  | complexStrategyDefinitionUpdateMessage (message : ComplexStrategyDefinitionUpdateMessage) -- "C" 0x43
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | simpleLiquiditySeekingEventNotificationMessage (message : SimpleLiquiditySeekingEventNotificationMessage) -- "L" 0x4C
  | complexLiquiditySeekingEventNotificationMessage (message : ComplexLiquiditySeekingEventNotificationMessage) -- "l" 0x6C
  | underlyingTradingStatusNotificationMessage (message : UnderlyingTradingStatusNotificationMessage) -- "H" 0x48
  | theoreticalSettlementReferencePriceNotificationMessage (message : TheoreticalSettlementReferencePriceNotificationMessage) -- "M" 0x4D
  | theoreticalSettlementPriceNotificationMessage (message : TheoreticalSettlementPriceNotificationMessage) -- "N" 0x4E
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .simpleSeriesUpdateMessage _ => 80
  | .complexStrategyDefinitionUpdateMessage _ => 67
  | .systemStateMessage _ => 83
  | .simpleLiquiditySeekingEventNotificationMessage _ => 76
  | .complexLiquiditySeekingEventNotificationMessage _ => 108
  | .underlyingTradingStatusNotificationMessage _ => 72
  | .theoreticalSettlementReferencePriceNotificationMessage _ => 77
  | .theoreticalSettlementPriceNotificationMessage _ => 78

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .simpleSeriesUpdateMessage message => SimpleSeriesUpdateMessage.encode message
  | .complexStrategyDefinitionUpdateMessage message => ComplexStrategyDefinitionUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .simpleLiquiditySeekingEventNotificationMessage message => SimpleLiquiditySeekingEventNotificationMessage.encode message
  | .complexLiquiditySeekingEventNotificationMessage message => ComplexLiquiditySeekingEventNotificationMessage.encode message
  | .underlyingTradingStatusNotificationMessage message => UnderlyingTradingStatusNotificationMessage.encode message
  | .theoreticalSettlementReferencePriceNotificationMessage message => TheoreticalSettlementReferencePriceNotificationMessage.encode message
  | .theoreticalSettlementPriceNotificationMessage message => TheoreticalSettlementPriceNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 3858 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | simpleSeriesUpdateMessage inner =>
    simp only [encode, SimpleSeriesUpdateMessage.encode_length]
    omega
  | complexStrategyDefinitionUpdateMessage inner =>
    have bound_inner := ComplexStrategyDefinitionUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | simpleLiquiditySeekingEventNotificationMessage inner =>
    simp only [encode, SimpleLiquiditySeekingEventNotificationMessage.encode_length]
    omega
  | complexLiquiditySeekingEventNotificationMessage inner =>
    simp only [encode, ComplexLiquiditySeekingEventNotificationMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [encode, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega
  | theoreticalSettlementReferencePriceNotificationMessage inner =>
    simp only [encode, TheoreticalSettlementReferencePriceNotificationMessage.encode_length]
    omega
  | theoreticalSettlementPriceNotificationMessage inner =>
    simp only [encode, TheoreticalSettlementPriceNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 80 then (SimpleSeriesUpdateMessage.decode bytes).map fun (message, rest) => (.simpleSeriesUpdateMessage message, rest)
  else if tag = 67 then (ComplexStrategyDefinitionUpdateMessage.decode bytes).map fun (message, rest) => (.complexStrategyDefinitionUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 76 then (SimpleLiquiditySeekingEventNotificationMessage.decode bytes).map fun (message, rest) => (.simpleLiquiditySeekingEventNotificationMessage message, rest)
  else if tag = 108 then (ComplexLiquiditySeekingEventNotificationMessage.decode bytes).map fun (message, rest) => (.complexLiquiditySeekingEventNotificationMessage message, rest)
  else if tag = 72 then (UnderlyingTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotificationMessage message, rest)
  else if tag = 77 then (TheoreticalSettlementReferencePriceNotificationMessage.decode bytes).map fun (message, rest) => (.theoreticalSettlementReferencePriceNotificationMessage message, rest)
  else if tag = 78 then (TheoreticalSettlementPriceNotificationMessage.decode bytes).map fun (message, rest) => (.theoreticalSettlementPriceNotificationMessage message, rest)
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
  | complexStrategyDefinitionUpdateMessage inner =>
    have bound_inner := ComplexStrategyDefinitionUpdateMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, encodeUInt_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | simpleLiquiditySeekingEventNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleLiquiditySeekingEventNotificationMessage.encode_length]
    omega
  | complexLiquiditySeekingEventNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ComplexLiquiditySeekingEventNotificationMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega
  | theoreticalSettlementReferencePriceNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TheoreticalSettlementReferencePriceNotificationMessage.encode_length]
    omega
  | theoreticalSettlementPriceNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TheoreticalSettlementPriceNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  | applicationMessage (message : ApplicationMessage) -- 3
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2
  | .applicationMessage _ => 3

def encode : Payload → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message
  | .applicationMessage message => ApplicationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 3859 := by
  cases message with
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Mach Message -/
structure MachMessage where
  sequenceNumber : BitVec 64
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encodeBody (message : MachMessage) : List UInt8 :=
  encodeUIntLE 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 1 message.sessionNumber
    ++ (Payload.encode message.payload))

def decodeBody (sequenceNumber : BitVec 64) (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let (sessionNumber, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, sessionNumber, payload }, bytes)

theorem decodeBody_encodeBody (message : MachMessage) (rest : List UInt8) :
    decodeBody message.sequenceNumber (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MachMessage) : (encodeBody message).length + 10 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 10, so it is written from the body and checked on decode; Sequence Number is read ahead of it -/
def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeFramedLE 2 10 encodeBody message)

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  decodeFramedLE 2 10 (decodeBody sequenceNumber) bytes

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFramedLE_encodeFramedLE 2 10 encodeBody (decodeBody message.sequenceNumber) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, encodeFramedLE_length]
  omega

end MachMessage

/-- Udp Packet -/
structure UdpPacket where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option UdpPacket := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end UdpPacket

end Omi.MiaxMiaxoptionsAisMachV26Udp
