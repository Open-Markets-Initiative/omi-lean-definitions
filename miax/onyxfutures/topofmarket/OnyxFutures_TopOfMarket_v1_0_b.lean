import Omi.Wire

/-!
# Miami International Holdings Top Of Market v1.0.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxOnyxfuturesTopofmarketMachV10B

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
  legRatioAndSide : BitVec 32
  maturityMonthYear : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentLeg

def encode (message : InstrumentLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.legRatioAndSide
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (InstrumentLeg × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioAndSide, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentId, legRatioAndSide, maturityMonthYear, reserved8 }, bytes)

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
  strategyId : BitVec 32
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
    ++ (encodeUIntLE 4 message.strategyId
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
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
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
    pure ({ timestamp, strategyId, underlyingAssetType, underlyingAsset, productGroupCode, spreadType, exchange, instrumentIdSource, instrumentType, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, tradingCollarVariationType, tradingCollarVariation, reserved16, instrumentLeg := ⟨instrumentLeg_, fits_instrumentLeg⟩ }, bytes)
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
  tomVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.tomVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tomVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ timestamp, tomVersion, sessionId, systemStatus }, bytes)

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

/-- Best Bid And Offer Message: 36 bytes -/
structure BestBidAndOfferMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  mbbPrice : BitVec 64
  mbbSize : BitVec 32
  mboPrice : BitVec 64
  mboSize : BitVec 32
  deriving DecidableEq, Repr

namespace BestBidAndOfferMessage

def encode (message : BestBidAndOfferMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.mbbPrice
    ++ (encodeUIntLE 4 message.mbbSize
    ++ (encodeUIntLE 8 message.mboPrice
    ++ (encodeUIntLE 4 message.mboSize)))))

def decode (bytes : List UInt8) : Option (BestBidAndOfferMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (mbbPrice, bytes) ← decodeUIntLE 8 bytes
  let (mbbSize, bytes) ← decodeUIntLE 4 bytes
  let (mboPrice, bytes) ← decodeUIntLE 8 bytes
  let (mboSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId, mbbPrice, mbbSize, mboPrice, mboSize }, bytes)

@[simp] theorem encode_length (message : BestBidAndOfferMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BestBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAndOfferMessage) (rest : List UInt8) :
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

end BestBidAndOfferMessage

/-- Last Sale Message: 32 bytes -/
structure LastSaleMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  tradeId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  deriving DecidableEq, Repr

namespace LastSaleMessage

def encode (message : LastSaleMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size))))

def decode (bytes : List UInt8) : Option (LastSaleMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId, tradeId, price, size }, bytes)

@[simp] theorem encode_length (message : LastSaleMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastSaleMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LastSaleMessage

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
  | bestBidAndOfferMessage (message : BestBidAndOfferMessage) -- 15
  | lastSaleMessage (message : LastSaleMessage) -- 16
  | tradeCancelMessage (message : TradeCancelMessage) -- 14
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .simpleInstrumentDefinitionMessage _ => 1
  | .complexInstrumentDefinitionMessage _ => 2
  | .systemStateMessage _ => 3
  | .instrumentTradingStatusNotificationMessage _ => 4
  | .bestBidAndOfferMessage _ => 15
  | .lastSaleMessage _ => 16
  | .tradeCancelMessage _ => 14

def encode : Data → List UInt8
  | .simpleInstrumentDefinitionMessage message => SimpleInstrumentDefinitionMessage.encode message
  | .complexInstrumentDefinitionMessage message => ComplexInstrumentDefinitionMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .instrumentTradingStatusNotificationMessage message => InstrumentTradingStatusNotificationMessage.encode message
  | .bestBidAndOfferMessage message => BestBidAndOfferMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
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
  | bestBidAndOfferMessage inner =>
    simp only [encode, BestBidAndOfferMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [encode, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 1 then (SimpleInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.simpleInstrumentDefinitionMessage message, rest)
  else if tag = 2 then (ComplexInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDefinitionMessage message, rest)
  else if tag = 3 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 4 then (InstrumentTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.instrumentTradingStatusNotificationMessage message, rest)
  else if tag = 15 then (BestBidAndOfferMessage.decode bytes).map fun (message, rest) => (.bestBidAndOfferMessage message, rest)
  else if tag = 16 then (LastSaleMessage.decode bytes).map fun (message, rest) => (.lastSaleMessage message, rest)
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
  | bestBidAndOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, BestBidAndOfferMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, LastSaleMessage.encode_length]
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

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | applicationMessage (message : ApplicationMessage) -- 3
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .applicationMessage _ => 3

def encode : Payload → List UInt8
  | .applicationMessage message => ApplicationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 5185 := by
  cases message with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Mach Message -/
structure MachMessage where
  sequenceNumber : BitVec 64
  packetLength : BitVec 16
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUIntLE 2 message.packetLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.sessionNumber
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (packetLength, bytes) ← decodeUIntLE 2 bytes
  let (packetType, bytes) ← decodeUInt 1 bytes
  let (sessionNumber, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, packetLength, sessionNumber, payload }, bytes)

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MachMessage) : (encode message).length ≤ 5197 := by
  unfold encode
  cases message.payload with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

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

end Omi.MiaxOnyxfuturesTopofmarketMachV10B
