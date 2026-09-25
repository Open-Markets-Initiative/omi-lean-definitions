import Omi.Wire

/-!
# Miami International Holdings Depth Of Market v1.0.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Modify Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxOnyxfuturesDepthofmarketMachV10B

/-- Underlying Asset Type: one byte code -/
def UnderlyingAssetType.codes : List UInt8 :=
  [0x45, 0x41]

inductive UnderlyingAssetType where
  | equityIndex -- Equity Index
  | commodityAgriculture -- Commodity Agriculture
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingAssetType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingAssetType

def toByte : UnderlyingAssetType → UInt8
  | .equityIndex => 0x45
  | .commodityAgriculture => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingAssetType :=
  if byte = 0x45 then .equityIndex
  else .commodityAgriculture

def ofByte (byte : UInt8) : UnderlyingAssetType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingAssetType) : ofByte value.toByte = value := by
  cases value with
  | equityIndex => decide
  | commodityAgriculture => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingAssetType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingAssetType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingAssetType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UnderlyingAssetType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingAssetType

/-- Instrument Id Source: one byte code -/
def InstrumentIdSource.codes : List UInt8 :=
  [0x45]

inductive InstrumentIdSource where
  | exchange -- Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentIdSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentIdSource

def toByte : InstrumentIdSource → UInt8
  | .exchange => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : InstrumentIdSource :=
  .exchange

def ofByte (byte : UInt8) : InstrumentIdSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentIdSource) : ofByte value.toByte = value := by
  cases value with
  | exchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentIdSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentIdSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentIdSource) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentIdSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentIdSource

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x46]

inductive InstrumentType where
  | futures -- Futures
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .futures => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : InstrumentType :=
  .futures

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | futures => decide
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

/-- Currency: one byte code -/
def Currency.codes : List UInt8 :=
  [0x55]

inductive Currency where
  | usd -- Usd
  | unlisted (byte : { byte : UInt8 // byte ∉ Currency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Currency

def toByte : Currency → UInt8
  | .usd => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Currency :=
  .usd

def ofByte (byte : UInt8) : Currency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Currency) : ofByte value.toByte = value := by
  cases value with
  | usd => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Currency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Currency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Currency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Currency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Currency

/-- Settlement Currency: one byte code -/
def SettlementCurrency.codes : List UInt8 :=
  [0x55]

inductive SettlementCurrency where
  | usd -- Usd
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementCurrency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementCurrency

def toByte : SettlementCurrency → UInt8
  | .usd => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SettlementCurrency :=
  .usd

def ofByte (byte : UInt8) : SettlementCurrency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementCurrency) : ofByte value.toByte = value := by
  cases value with
  | usd => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementCurrency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementCurrency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementCurrency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementCurrency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementCurrency

/-- Match Algorithm: one byte code -/
def MatchAlgorithm.codes : List UInt8 :=
  [0x50]

inductive MatchAlgorithm where
  | priceThenTime -- Price Then Time
  | unlisted (byte : { byte : UInt8 // byte ∉ MatchAlgorithm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MatchAlgorithm

def toByte : MatchAlgorithm → UInt8
  | .priceThenTime => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MatchAlgorithm :=
  .priceThenTime

def ofByte (byte : UInt8) : MatchAlgorithm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MatchAlgorithm) : ofByte value.toByte = value := by
  cases value with
  | priceThenTime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MatchAlgorithm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MatchAlgorithm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MatchAlgorithm) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MatchAlgorithm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MatchAlgorithm

/-- Settlement Price Type Calc Method: one byte code -/
def SettlementPriceTypeCalcMethod.codes : List UInt8 :=
  [0x41, 0x54]

inductive SettlementPriceTypeCalcMethod where
  | actual -- Actual
  | theoretical -- Theoretical
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementPriceTypeCalcMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementPriceTypeCalcMethod

def toByte : SettlementPriceTypeCalcMethod → UInt8
  | .actual => 0x41
  | .theoretical => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementPriceTypeCalcMethod :=
  if byte = 0x41 then .actual
  else .theoretical

def ofByte (byte : UInt8) : SettlementPriceTypeCalcMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementPriceTypeCalcMethod) : ofByte value.toByte = value := by
  cases value with
  | actual => decide
  | theoretical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementPriceTypeCalcMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementPriceTypeCalcMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementPriceTypeCalcMethod) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementPriceTypeCalcMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementPriceTypeCalcMethod

/-- Trading Collar Variation Type: one byte code -/
def TradingCollarVariationType.codes : List UInt8 :=
  [0x44, 0x50, 0x53, 0x45, 0x42]

inductive TradingCollarVariationType where
  | productDollarCollarValue -- Product Dollar Collar Value
  | productCollarPercentageValue -- Product Collar Percentage Value
  | standardCalendarSpread -- Standard Calendar Spread
  | equityCalendarSpread -- Equity Calendar Spread
  | butterflySpread -- Butterfly Spread
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingCollarVariationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingCollarVariationType

def toByte : TradingCollarVariationType → UInt8
  | .productDollarCollarValue => 0x44
  | .productCollarPercentageValue => 0x50
  | .standardCalendarSpread => 0x53
  | .equityCalendarSpread => 0x45
  | .butterflySpread => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingCollarVariationType :=
  if byte = 0x44 then .productDollarCollarValue
  else if byte = 0x50 then .productCollarPercentageValue
  else if byte = 0x53 then .standardCalendarSpread
  else if byte = 0x45 then .equityCalendarSpread
  else .butterflySpread

def ofByte (byte : UInt8) : TradingCollarVariationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingCollarVariationType) : ofByte value.toByte = value := by
  cases value with
  | productDollarCollarValue => decide
  | productCollarPercentageValue => decide
  | standardCalendarSpread => decide
  | equityCalendarSpread => decide
  | butterflySpread => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingCollarVariationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingCollarVariationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingCollarVariationType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingCollarVariationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingCollarVariationType

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

/-- Settlement Price Type: one byte code -/
def SettlementPriceType.codes : List UInt8 :=
  [0x44, 0x46]

inductive SettlementPriceType where
  | daily -- Daily
  | final -- Final
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementPriceType

def toByte : SettlementPriceType → UInt8
  | .daily => 0x44
  | .final => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementPriceType :=
  if byte = 0x44 then .daily
  else .final

def ofByte (byte : UInt8) : SettlementPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementPriceType) : ofByte value.toByte = value := by
  cases value with
  | daily => decide
  | final => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementPriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementPriceType

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x53, 0x43, 0x44]

inductive OrderType where
  | simpleOrder -- Simple Order
  | complexOrder -- Complex Order
  | derivedOrder -- Derived Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .simpleOrder => 0x53
  | .complexOrder => 0x43
  | .derivedOrder => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x53 then .simpleOrder
  else if byte = 0x43 then .complexOrder
  else .derivedOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | simpleOrder => decide
  | complexOrder => decide
  | derivedOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

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

/-- Aggressor Side: one byte code -/
def AggressorSide.codes : List UInt8 :=
  [0x42, 0x53, 0x4E]

inductive AggressorSide where
  | buy -- Buy
  | sell -- Sell
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorSide

def toByte : AggressorSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .notApplicable

def ofByte (byte : UInt8) : AggressorSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AggressorSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorSide

/-- Simple Instrument Definition Message: 119 bytes -/
structure SimpleInstrumentDefinitionMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  underlyingAssetType : UnderlyingAssetType
  underlyingAsset : Alpha 4
  productGroupCode : Alpha 6
  exchange : Alpha 4
  instrumentIdSource : InstrumentIdSource
  instrumentType : InstrumentType
  maturityMonthYear : BitVec 32
  currency : Currency
  settlementCurrency : SettlementCurrency
  matchAlgorithm : MatchAlgorithm
  minimumSize : BitVec 32
  maximumSize : BitVec 32
  tick : BitVec 64
  unitOfMeasure : Alpha 5
  unitOfMeasureQuantity : BitVec 32
  settlementPrice : BitVec 64
  settlementPriceTypeCalcMethod : SettlementPriceTypeCalcMethod
  totalVolume : BitVec 32
  openInterestQuantity : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  tradingCollarVariationType : TradingCollarVariationType
  tradingCollarVariation : BitVec 64
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SimpleInstrumentDefinitionMessage

def encode (message : SimpleInstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (UnderlyingAssetType.encode message.underlyingAssetType
    ++ (Alpha.encode message.underlyingAsset
    ++ (Alpha.encode message.productGroupCode
    ++ (Alpha.encode message.exchange
    ++ (InstrumentIdSource.encode message.instrumentIdSource
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (Currency.encode message.currency
    ++ (SettlementCurrency.encode message.settlementCurrency
    ++ (MatchAlgorithm.encode message.matchAlgorithm
    ++ (encodeUIntLE 4 message.minimumSize
    ++ (encodeUIntLE 4 message.maximumSize
    ++ (encodeUIntLE 8 message.tick
    ++ (Alpha.encode message.unitOfMeasure
    ++ (encodeUIntLE 4 message.unitOfMeasureQuantity
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (SettlementPriceTypeCalcMethod.encode message.settlementPriceTypeCalcMethod
    ++ (encodeUIntLE 4 message.totalVolume
    ++ (encodeUIntLE 4 message.openInterestQuantity
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (TradingCollarVariationType.encode message.tradingCollarVariationType
    ++ (encodeUIntLE 8 message.tradingCollarVariation
    ++ (Alpha.encode message.reserved16)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SimpleInstrumentDefinitionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingAssetType, bytes) ← UnderlyingAssetType.decode bytes
  let (underlyingAsset, bytes) ← Alpha.decode 4 bytes
  let (productGroupCode, bytes) ← Alpha.decode 6 bytes
  let (exchange, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdSource, bytes) ← InstrumentIdSource.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Currency.decode bytes
  let (settlementCurrency, bytes) ← SettlementCurrency.decode bytes
  let (matchAlgorithm, bytes) ← MatchAlgorithm.decode bytes
  let (minimumSize, bytes) ← decodeUIntLE 4 bytes
  let (maximumSize, bytes) ← decodeUIntLE 4 bytes
  let (tick, bytes) ← decodeUIntLE 8 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureQuantity, bytes) ← decodeUIntLE 4 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPriceTypeCalcMethod, bytes) ← SettlementPriceTypeCalcMethod.decode bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  let (openInterestQuantity, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingCollarVariationType, bytes) ← TradingCollarVariationType.decode bytes
  let (tradingCollarVariation, bytes) ← decodeUIntLE 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ timestamp, instrumentId, underlyingAssetType, underlyingAsset, productGroupCode, exchange, instrumentIdSource, instrumentType, maturityMonthYear, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, settlementPrice, settlementPriceTypeCalcMethod, totalVolume, openInterestQuantity, highLimitPrice, lowLimitPrice, tradingCollarVariationType, tradingCollarVariation, reserved16 }, bytes)

@[simp] theorem encode_length (message : SimpleInstrumentDefinitionMessage) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, UnderlyingAssetType.encode_length, Alpha.encode_length, InstrumentIdSource.encode_length, InstrumentType.encode_length, Currency.encode_length, SettlementCurrency.encode_length, MatchAlgorithm.encode_length, SettlementPriceTypeCalcMethod.encode_length, TradingCollarVariationType.encode_length]

theorem encode_length_pos (message : SimpleInstrumentDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SimpleInstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingAssetType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentIdSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Currency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCurrency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MatchAlgorithm.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlementPriceTypeCalcMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingCollarVariationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleInstrumentDefinitionMessage

/-- Instrument Leg: 20 bytes -/
structure InstrumentLeg where
  instrumentId : BitVec 32
  legRatio : BitVec 32
  maturityMonthYear : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentLeg

def encode (message : InstrumentLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.legRatio
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (InstrumentLeg × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentId, legRatio, maturityMonthYear, reserved8 }, bytes)

@[simp] theorem encode_length (message : InstrumentLeg) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentLeg

/-- Complex Instrument Definition Message -/
structure ComplexInstrumentDefinitionMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  underlyingAssetType : UnderlyingAssetType
  underlyingAsset : Alpha 4
  productGroupCode : Alpha 6
  spreadType : Alpha 1
  exchange : Alpha 4
  instrumentIdSource : InstrumentIdSource
  instrumentType : InstrumentType
  currency : Currency
  settlementCurrency : SettlementCurrency
  matchAlgorithm : MatchAlgorithm
  minimumSize : BitVec 32
  maximumSize : BitVec 32
  tick : BitVec 64
  unitOfMeasure : Alpha 5
  unitOfMeasureQuantity : BitVec 32
  tradingCollarVariationType : TradingCollarVariationType
  tradingCollarVariation : BitVec 64
  reserved16 : Alpha 16
  instrumentLeg : Bounded 1 InstrumentLeg
  deriving DecidableEq, Repr

namespace ComplexInstrumentDefinitionMessage

def encode (message : ComplexInstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (UnderlyingAssetType.encode message.underlyingAssetType
    ++ (Alpha.encode message.underlyingAsset
    ++ (Alpha.encode message.productGroupCode
    ++ (Alpha.encode message.spreadType
    ++ (Alpha.encode message.exchange
    ++ (InstrumentIdSource.encode message.instrumentIdSource
    ++ (InstrumentType.encode message.instrumentType
    ++ (Currency.encode message.currency
    ++ (SettlementCurrency.encode message.settlementCurrency
    ++ (MatchAlgorithm.encode message.matchAlgorithm
    ++ (encodeUIntLE 4 message.minimumSize
    ++ (encodeUIntLE 4 message.maximumSize
    ++ (encodeUIntLE 8 message.tick
    ++ (Alpha.encode message.unitOfMeasure
    ++ (encodeUIntLE 4 message.unitOfMeasureQuantity
    ++ (TradingCollarVariationType.encode message.tradingCollarVariationType
    ++ (encodeUIntLE 8 message.tradingCollarVariation
    ++ (Alpha.encode message.reserved16
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.instrumentLeg.val.length)
    ++ (encodeMany InstrumentLeg.encode message.instrumentLeg.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexInstrumentDefinitionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingAssetType, bytes) ← UnderlyingAssetType.decode bytes
  let (underlyingAsset, bytes) ← Alpha.decode 4 bytes
  let (productGroupCode, bytes) ← Alpha.decode 6 bytes
  let (spreadType, bytes) ← Alpha.decode 1 bytes
  let (exchange, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdSource, bytes) ← InstrumentIdSource.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (currency, bytes) ← Currency.decode bytes
  let (settlementCurrency, bytes) ← SettlementCurrency.decode bytes
  let (matchAlgorithm, bytes) ← MatchAlgorithm.decode bytes
  let (minimumSize, bytes) ← decodeUIntLE 4 bytes
  let (maximumSize, bytes) ← decodeUIntLE 4 bytes
  let (tick, bytes) ← decodeUIntLE 8 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureQuantity, bytes) ← decodeUIntLE 4 bytes
  let (tradingCollarVariationType, bytes) ← TradingCollarVariationType.decode bytes
  let (tradingCollarVariation, bytes) ← decodeUIntLE 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (instrumentLeg_, bytes) ← decodeMany InstrumentLeg.decode numberOfLegs.toNat bytes
  if fits_instrumentLeg : instrumentLeg_.length < 256 ^ 1 then
    pure ({ timestamp, instrumentId, underlyingAssetType, underlyingAsset, productGroupCode, spreadType, exchange, instrumentIdSource, instrumentType, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, tradingCollarVariationType, tradingCollarVariation, reserved16, instrumentLeg := ⟨instrumentLeg_, fits_instrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexInstrumentDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexInstrumentDefinitionMessage) : (encode message).length ≤ 5184 := by
  have bound_instrumentLeg := message.instrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnderlyingAssetType.encode_length, Alpha.encode_length, InstrumentIdSource.encode_length, InstrumentType.encode_length, Currency.encode_length, SettlementCurrency.encode_length, MatchAlgorithm.encode_length, TradingCollarVariationType.encode_length, encodeMany_length_const InstrumentLeg.encode 20 InstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexInstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingAssetType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentIdSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Currency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCurrency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MatchAlgorithm.decode_encode, some_bind]
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
  rw [List.append_assoc, TradingCollarVariationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstrumentLeg.encode InstrumentLeg.decode InstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentLeg.length_lt]
  rfl

end ComplexInstrumentDefinitionMessage

/-- System State Message: 18 bytes -/
structure SystemStateMessage where
  timestamp : BitVec 64
  domVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.domVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (domVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ timestamp, domVersion, sessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemStateMessage) : (encode message).length = 18 := by
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

/-- Instrument Trading Status Notification Message: 14 bytes -/
structure InstrumentTradingStatusNotificationMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  tradingStatus : BitVec 8
  marketState : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentTradingStatusNotificationMessage

def encode (message : InstrumentTradingStatusNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketState)))

def decode (bytes : List UInt8) : Option (InstrumentTradingStatusNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketState, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrumentId, tradingStatus, marketState }, bytes)

@[simp] theorem encode_length (message : InstrumentTradingStatusNotificationMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentTradingStatusNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentTradingStatusNotificationMessage) (rest : List UInt8) :
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

end InstrumentTradingStatusNotificationMessage

/-- Anticipated Opening Price Message: 24 bytes -/
structure AnticipatedOpeningPriceMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  anticipatedOpeningPrice : BitVec 64
  openingMatchQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace AnticipatedOpeningPriceMessage

def encode (message : AnticipatedOpeningPriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.anticipatedOpeningPrice
    ++ (encodeUIntLE 4 message.openingMatchQuantity)))

def decode (bytes : List UInt8) : Option (AnticipatedOpeningPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (anticipatedOpeningPrice, bytes) ← decodeUIntLE 8 bytes
  let (openingMatchQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId, anticipatedOpeningPrice, openingMatchQuantity }, bytes)

@[simp] theorem encode_length (message : AnticipatedOpeningPriceMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AnticipatedOpeningPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AnticipatedOpeningPriceMessage) (rest : List UInt8) :
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

end AnticipatedOpeningPriceMessage

/-- Settlement Price Update Message: 24 bytes -/
structure SettlementPriceUpdateMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  settlementPrice : BitVec 64
  settlementPriceType : SettlementPriceType
  settlementPriceTypeCalcMethod : SettlementPriceTypeCalcMethod
  deriving DecidableEq, Repr

namespace SettlementPriceUpdateMessage

def encode (message : SettlementPriceUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (SettlementPriceType.encode message.settlementPriceType
    ++ (SettlementPriceTypeCalcMethod.encode message.settlementPriceTypeCalcMethod)))))

def decode (bytes : List UInt8) : Option (SettlementPriceUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPriceType, bytes) ← SettlementPriceType.decode bytes
  let (settlementPriceTypeCalcMethod, bytes) ← SettlementPriceTypeCalcMethod.decode bytes
  pure ({ timestamp, tradeDate, instrumentId, settlementPrice, settlementPriceType, settlementPriceTypeCalcMethod }, bytes)

@[simp] theorem encode_length (message : SettlementPriceUpdateMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SettlementPriceType.encode_length, SettlementPriceTypeCalcMethod.encode_length]

theorem encode_length_pos (message : SettlementPriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPriceUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SettlementPriceType.decode_encode, some_bind]
  dsimp only
  rw [SettlementPriceTypeCalcMethod.decode_encode, some_bind]
  rfl

end SettlementPriceUpdateMessage

/-- Open Interest Update Message: 18 bytes -/
structure OpenInterestUpdateMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  openInterestQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestUpdateMessage

def encode (message : OpenInterestUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.openInterestQuantity)))

def decode (bytes : List UInt8) : Option (OpenInterestUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (openInterestQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, tradeDate, instrumentId, openInterestQuantity }, bytes)

@[simp] theorem encode_length (message : OpenInterestUpdateMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OpenInterestUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestUpdateMessage) (rest : List UInt8) :
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

end OpenInterestUpdateMessage

/-- Total Volume Update Message: 18 bytes -/
structure TotalVolumeUpdateMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  totalVolume : BitVec 32
  deriving DecidableEq, Repr

namespace TotalVolumeUpdateMessage

def encode (message : TotalVolumeUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.totalVolume)))

def decode (bytes : List UInt8) : Option (TotalVolumeUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, tradeDate, instrumentId, totalVolume }, bytes)

@[simp] theorem encode_length (message : TotalVolumeUpdateMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TotalVolumeUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TotalVolumeUpdateMessage) (rest : List UInt8) :
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

end TotalVolumeUpdateMessage

/-- Instrument Clear Message: 12 bytes -/
structure InstrumentClearMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace InstrumentClearMessage

def encode (message : InstrumentClearMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId)

def decode (bytes : List UInt8) : Option (InstrumentClearMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId }, bytes)

@[simp] theorem encode_length (message : InstrumentClearMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentClearMessage

/-- Add Order Message: 34 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderType : OrderType
  orderId : BitVec 64
  orderSide : OrderSide
  price : BitVec 64
  size : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 8 message.orderId
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId, orderType, orderId, orderSide, price, size }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderType.encode_length, OrderSide.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMessage

/-- Modify Order Message: 33 bytes -/
structure ModifyOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  modifyFlags : BitVec 8
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.modifyFlags)))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (modifyFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrumentId, orderId, price, size, modifyFlags }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrderMessage

/-- Delete Order Message: 20 bytes -/
structure DeleteOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrumentId, orderId }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOrderMessage

/-- Order Execution Message: 52 bytes -/
structure OrderExecutionMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  aggressorSide : AggressorSide
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutionMessage

def encode (message : OrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (AggressorSide.encode message.aggressorSide
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size)))))))))

def decode (bytes : List UInt8) : Option (OrderExecutionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← AggressorSide.decode bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, tradeDate, instrumentId, buyOrderId, sellOrderId, aggressorSide, tradeId, correctionNumber, price, size }, bytes)

@[simp] theorem encode_length (message : OrderExecutionMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AggressorSide.encode_length]

theorem encode_length_pos (message : OrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AggressorSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutionMessage

/-- Trade Cancel Message: 35 bytes -/
structure TradeCancelMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size))))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, tradeDate, instrumentId, tradeId, correctionNumber, price, size }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | simpleInstrumentDefinitionMessage (message : SimpleInstrumentDefinitionMessage) -- 1
  | complexInstrumentDefinitionMessage (message : ComplexInstrumentDefinitionMessage) -- 2
  | systemStateMessage (message : SystemStateMessage) -- 3
  | instrumentTradingStatusNotificationMessage (message : InstrumentTradingStatusNotificationMessage) -- 4
  | anticipatedOpeningPriceMessage (message : AnticipatedOpeningPriceMessage) -- 5
  | settlementPriceUpdateMessage (message : SettlementPriceUpdateMessage) -- 6
  | openInterestUpdateMessage (message : OpenInterestUpdateMessage) -- 7
  | totalVolumeUpdateMessage (message : TotalVolumeUpdateMessage) -- 8
  | instrumentClearMessage (message : InstrumentClearMessage) -- 9
  | addOrderMessage (message : AddOrderMessage) -- 10
  | modifyOrderMessage (message : ModifyOrderMessage) -- 11
  | deleteOrderMessage (message : DeleteOrderMessage) -- 12
  | orderExecutionMessage (message : OrderExecutionMessage) -- 13
  | tradeCancelMessage (message : TradeCancelMessage) -- 14
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .simpleInstrumentDefinitionMessage _ => 1
  | .complexInstrumentDefinitionMessage _ => 2
  | .systemStateMessage _ => 3
  | .instrumentTradingStatusNotificationMessage _ => 4
  | .anticipatedOpeningPriceMessage _ => 5
  | .settlementPriceUpdateMessage _ => 6
  | .openInterestUpdateMessage _ => 7
  | .totalVolumeUpdateMessage _ => 8
  | .instrumentClearMessage _ => 9
  | .addOrderMessage _ => 10
  | .modifyOrderMessage _ => 11
  | .deleteOrderMessage _ => 12
  | .orderExecutionMessage _ => 13
  | .tradeCancelMessage _ => 14

def encode : Data → List UInt8
  | .simpleInstrumentDefinitionMessage message => SimpleInstrumentDefinitionMessage.encode message
  | .complexInstrumentDefinitionMessage message => ComplexInstrumentDefinitionMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .instrumentTradingStatusNotificationMessage message => InstrumentTradingStatusNotificationMessage.encode message
  | .anticipatedOpeningPriceMessage message => AnticipatedOpeningPriceMessage.encode message
  | .settlementPriceUpdateMessage message => SettlementPriceUpdateMessage.encode message
  | .openInterestUpdateMessage message => OpenInterestUpdateMessage.encode message
  | .totalVolumeUpdateMessage message => TotalVolumeUpdateMessage.encode message
  | .instrumentClearMessage message => InstrumentClearMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .orderExecutionMessage message => OrderExecutionMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 5184 := by
  cases message with
  | simpleInstrumentDefinitionMessage inner =>
    simp only [encode, SimpleInstrumentDefinitionMessage.encode_length]
    omega
  | complexInstrumentDefinitionMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | instrumentTradingStatusNotificationMessage inner =>
    simp only [encode, InstrumentTradingStatusNotificationMessage.encode_length]
    omega
  | anticipatedOpeningPriceMessage inner =>
    simp only [encode, AnticipatedOpeningPriceMessage.encode_length]
    omega
  | settlementPriceUpdateMessage inner =>
    simp only [encode, SettlementPriceUpdateMessage.encode_length]
    omega
  | openInterestUpdateMessage inner =>
    simp only [encode, OpenInterestUpdateMessage.encode_length]
    omega
  | totalVolumeUpdateMessage inner =>
    simp only [encode, TotalVolumeUpdateMessage.encode_length]
    omega
  | instrumentClearMessage inner =>
    simp only [encode, InstrumentClearMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [encode, DeleteOrderMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [encode, OrderExecutionMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 1 then (SimpleInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.simpleInstrumentDefinitionMessage message, rest)
  else if tag = 2 then (ComplexInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDefinitionMessage message, rest)
  else if tag = 3 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 4 then (InstrumentTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.instrumentTradingStatusNotificationMessage message, rest)
  else if tag = 5 then (AnticipatedOpeningPriceMessage.decode bytes).map fun (message, rest) => (.anticipatedOpeningPriceMessage message, rest)
  else if tag = 6 then (SettlementPriceUpdateMessage.decode bytes).map fun (message, rest) => (.settlementPriceUpdateMessage message, rest)
  else if tag = 7 then (OpenInterestUpdateMessage.decode bytes).map fun (message, rest) => (.openInterestUpdateMessage message, rest)
  else if tag = 8 then (TotalVolumeUpdateMessage.decode bytes).map fun (message, rest) => (.totalVolumeUpdateMessage message, rest)
  else if tag = 9 then (InstrumentClearMessage.decode bytes).map fun (message, rest) => (.instrumentClearMessage message, rest)
  else if tag = 10 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 11 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 12 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 13 then (OrderExecutionMessage.decode bytes).map fun (message, rest) => (.orderExecutionMessage message, rest)
  else if tag = 14 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
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
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 5185 := by
  unfold encode
  cases message.data with
  | simpleInstrumentDefinitionMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleInstrumentDefinitionMessage.encode_length]
    omega
  | complexInstrumentDefinitionMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, encodeUInt_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | instrumentTradingStatusNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, InstrumentTradingStatusNotificationMessage.encode_length]
    omega
  | anticipatedOpeningPriceMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, AnticipatedOpeningPriceMessage.encode_length]
    omega
  | settlementPriceUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SettlementPriceUpdateMessage.encode_length]
    omega
  | openInterestUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, OpenInterestUpdateMessage.encode_length]
    omega
  | totalVolumeUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TotalVolumeUpdateMessage.encode_length]
    omega
  | instrumentClearMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, InstrumentClearMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, DeleteOrderMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, OrderExecutionMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TradeCancelMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

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

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | applicationMessage (message : ApplicationMessage) -- 3
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .applicationMessage _ => 3
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2

def encode : Payload → List UInt8
  | .applicationMessage message => ApplicationMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 5185 := by
  cases message with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.sessionNumber
    ++ (Payload.encode message.payload))

def decodeBody (sequenceNumber : BitVec 64) (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (packetType, bytes) ← decodeUInt 1 bytes
  let (sessionNumber, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, sessionNumber, payload }, bytes)

theorem decodeBody_encodeBody (message : MachMessage) (rest : List UInt8) :
    decodeBody message.sequenceNumber (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MachMessage) : (encodeBody message).length + 10 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, EndOfSession.encode_length]
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

/-- Packet -/
structure Packet where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option Packet := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end Packet

end Omi.MiaxOnyxfuturesDepthofmarketMachV10B
