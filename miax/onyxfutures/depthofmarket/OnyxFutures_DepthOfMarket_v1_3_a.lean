import Wire

/-!
# Miami International Holdings Depth Of Market v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxOnyxfuturesDepthofmarketMachV13A

/-- Underlying Asset Type: one byte code -/
def UnderlyingAssetType.codes : List UInt8 :=
  [0x45, 0x41, 0x46, 0x4E]

inductive UnderlyingAssetType where
  | equity -- Equity
  | commodityAgriculture -- Commodity Agriculture
  | futures -- Futures
  | not -- Not
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingAssetType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingAssetType

def toByte : UnderlyingAssetType → UInt8
  | .equity => 0x45
  | .commodityAgriculture => 0x41
  | .futures => 0x46
  | .not => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingAssetType :=
  if byte = 0x45 then .equity
  else if byte = 0x41 then .commodityAgriculture
  else if byte = 0x46 then .futures
  else .not

def ofByte (byte : UInt8) : UnderlyingAssetType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingAssetType) : ofByte value.toByte = value := by
  cases value with
  | equity => decide
  | commodityAgriculture => decide
  | futures => decide
  | not => decide
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
  [0x46, 0x4F, 0x54, 0x42]

inductive InstrumentType where
  | futures -- Futures
  | optionsOn -- Options On
  | tradeAt -- Trade At
  | basis -- Basis
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .futures => 0x46
  | .optionsOn => 0x4F
  | .tradeAt => 0x54
  | .basis => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x46 then .futures
  else if byte = 0x4F then .optionsOn
  else if byte = 0x54 then .tradeAt
  else .basis

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | futures => decide
  | optionsOn => decide
  | tradeAt => decide
  | basis => decide
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

/-- Instrument Listing Status: one byte code -/
def InstrumentListingStatus.codes : List UInt8 :=
  [0x41, 0x49]

inductive InstrumentListingStatus where
  | active -- Active
  | inactive -- Inactive
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentListingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentListingStatus

def toByte : InstrumentListingStatus → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentListingStatus :=
  if byte = 0x41 then .active
  else .inactive

def ofByte (byte : UInt8) : InstrumentListingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentListingStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentListingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentListingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentListingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentListingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentListingStatus

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
  | priceTime -- Price Time
  | unlisted (byte : { byte : UInt8 // byte ∉ MatchAlgorithm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MatchAlgorithm

def toByte : MatchAlgorithm → UInt8
  | .priceTime => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MatchAlgorithm :=
  .priceTime

def ofByte (byte : UInt8) : MatchAlgorithm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MatchAlgorithm) : ofByte value.toByte = value := by
  cases value with
  | priceTime => decide
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
  [0x44, 0x50, 0x4E]

inductive TradingCollarVariationType where
  | product -- Product
  | product_50 -- Product
  | not -- Not
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingCollarVariationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingCollarVariationType

def toByte : TradingCollarVariationType → UInt8
  | .product => 0x44
  | .product_50 => 0x50
  | .not => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingCollarVariationType :=
  if byte = 0x44 then .product
  else if byte = 0x50 then .product_50
  else .not

def ofByte (byte : UInt8) : TradingCollarVariationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingCollarVariationType) : ofByte value.toByte = value := by
  cases value with
  | product => decide
  | product_50 => decide
  | not => decide
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

/-- Option Strike Currency: one byte code -/
def OptionStrikeCurrency.codes : List UInt8 :=
  [0x55, 0x4E]

inductive OptionStrikeCurrency where
  | usDollar -- Us Dollar
  | naWhen -- Na When
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionStrikeCurrency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionStrikeCurrency

def toByte : OptionStrikeCurrency → UInt8
  | .usDollar => 0x55
  | .naWhen => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionStrikeCurrency :=
  if byte = 0x55 then .usDollar
  else .naWhen

def ofByte (byte : UInt8) : OptionStrikeCurrency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionStrikeCurrency) : ofByte value.toByte = value := by
  cases value with
  | usDollar => decide
  | naWhen => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionStrikeCurrency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionStrikeCurrency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionStrikeCurrency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionStrikeCurrency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionStrikeCurrency

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x4E]

inductive OptionType where
  | call -- Call
  | put -- Put
  | naWhen -- Na When
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .naWhen => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .naWhen

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | naWhen => decide
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

/-- Option Expiration Type: one byte code -/
def OptionExpirationType.codes : List UInt8 :=
  [0x41, 0x45, 0x4E]

inductive OptionExpirationType where
  | americanStyle -- American Style
  | europeanStyle -- European Style
  | naWhen -- Na When
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionExpirationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionExpirationType

def toByte : OptionExpirationType → UInt8
  | .americanStyle => 0x41
  | .europeanStyle => 0x45
  | .naWhen => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionExpirationType :=
  if byte = 0x41 then .americanStyle
  else if byte = 0x45 then .europeanStyle
  else .naWhen

def ofByte (byte : UInt8) : OptionExpirationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionExpirationType) : ofByte value.toByte = value := by
  cases value with
  | americanStyle => decide
  | europeanStyle => decide
  | naWhen => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionExpirationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionExpirationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionExpirationType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionExpirationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionExpirationType

/-- Spread Type: one byte code -/
def SpreadType.codes : List UInt8 :=
  [0x53, 0x45, 0x42, 0x43]

inductive SpreadType where
  | standard -- Standard
  | equity -- Equity
  | butterfly -- Butterfly
  | cross -- Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ SpreadType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpreadType

def toByte : SpreadType → UInt8
  | .standard => 0x53
  | .equity => 0x45
  | .butterfly => 0x42
  | .cross => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpreadType :=
  if byte = 0x53 then .standard
  else if byte = 0x45 then .equity
  else if byte = 0x42 then .butterfly
  else .cross

def ofByte (byte : UInt8) : SpreadType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpreadType) : ofByte value.toByte = value := by
  cases value with
  | standard => decide
  | equity => decide
  | butterfly => decide
  | cross => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpreadType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpreadType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpreadType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpreadType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpreadType

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32]

inductive SystemStatus where
  | startOf -- Start Of
  | endOf -- End Of
  | startOf_31 -- Start Of
  | endOf_32 -- End Of
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOf => 0x53
  | .endOf => 0x43
  | .startOf_31 => 0x31
  | .endOf_32 => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOf
  else if byte = 0x43 then .endOf
  else if byte = 0x31 then .startOf_31
  else .endOf_32

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOf => decide
  | endOf => decide
  | startOf_31 => decide
  | endOf_32 => decide
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
  | simple -- Simple
  | complex -- Complex
  | derived -- Derived
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .simple => 0x53
  | .complex => 0x43
  | .derived => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x53 then .simple
  else if byte = 0x43 then .complex
  else .derived

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | simple => decide
  | complex => decide
  | derived => decide
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
  | not -- Not
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorSide

def toByte : AggressorSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .not => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .not

def ofByte (byte : UInt8) : AggressorSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | not => decide
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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4F, 0x53, 0x4D, 0x43, 0x4C, 0x41]

inductive TradeType where
  | outright -- Outright
  | strategy -- Strategy
  | strategy_4d -- Strategy
  | complex -- Complex
  | complex_4c -- Complex
  | adjustedLate -- Adjusted Late
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .outright => 0x4F
  | .strategy => 0x53
  | .strategy_4d => 0x4D
  | .complex => 0x43
  | .complex_4c => 0x4C
  | .adjustedLate => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4F then .outright
  else if byte = 0x53 then .strategy
  else if byte = 0x4D then .strategy_4d
  else if byte = 0x43 then .complex
  else if byte = 0x4C then .complex_4c
  else .adjustedLate

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | outright => decide
  | strategy => decide
  | strategy_4d => decide
  | complex => decide
  | complex_4c => decide
  | adjustedLate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Simple Instrument Definition Message: 138 bytes -/
structure SimpleInstrumentDefinitionMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  underlyingAssetType : UnderlyingAssetType
  underlyingAssetAlphanumeric4 : Alpha 4
  productGroupCodeAlphanumeric6 : Alpha 6
  exchange : Alpha 4
  instrumentIdSource : InstrumentIdSource
  instrumentType : InstrumentType
  instrumentListingStatus : InstrumentListingStatus
  reserved3 : Alpha 3
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
  contractDate : BitVec 32
  maturityDate : BitVec 16
  valuationDate : BitVec 16
  firstTradeDate : BitVec 16
  lastTradeDate : BitVec 16
  firstNoticeDate : BitVec 16
  lastNoticeDate : BitVec 16
  firstDeliveryDate : BitVec 16
  lastDeliveryDate : BitVec 16
  optionStrikePrice : BitVec 64
  optionStrikeCurrency : OptionStrikeCurrency
  optionType : OptionType
  optionExpirationType : OptionExpirationType
  underlyingFutureInstrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace SimpleInstrumentDefinitionMessage

def encode (message : SimpleInstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (UnderlyingAssetType.encode message.underlyingAssetType
    ++ (Alpha.encode message.underlyingAssetAlphanumeric4
    ++ (Alpha.encode message.productGroupCodeAlphanumeric6
    ++ (Alpha.encode message.exchange
    ++ (InstrumentIdSource.encode message.instrumentIdSource
    ++ (InstrumentType.encode message.instrumentType
    ++ (InstrumentListingStatus.encode message.instrumentListingStatus
    ++ (Alpha.encode message.reserved3
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
    ++ (encodeUIntLE 4 message.contractDate
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (encodeUIntLE 2 message.valuationDate
    ++ (encodeUIntLE 2 message.firstTradeDate
    ++ (encodeUIntLE 2 message.lastTradeDate
    ++ (encodeUIntLE 2 message.firstNoticeDate
    ++ (encodeUIntLE 2 message.lastNoticeDate
    ++ (encodeUIntLE 2 message.firstDeliveryDate
    ++ (encodeUIntLE 2 message.lastDeliveryDate
    ++ (encodeUIntLE 8 message.optionStrikePrice
    ++ (OptionStrikeCurrency.encode message.optionStrikeCurrency
    ++ (OptionType.encode message.optionType
    ++ (OptionExpirationType.encode message.optionExpirationType
    ++ (encodeUIntLE 4 message.underlyingFutureInstrumentId)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SimpleInstrumentDefinitionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingAssetType, bytes) ← UnderlyingAssetType.decode bytes
  let (underlyingAssetAlphanumeric4, bytes) ← Alpha.decode 4 bytes
  let (productGroupCodeAlphanumeric6, bytes) ← Alpha.decode 6 bytes
  let (exchange, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdSource, bytes) ← InstrumentIdSource.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (instrumentListingStatus, bytes) ← InstrumentListingStatus.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
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
  let (contractDate, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (valuationDate, bytes) ← decodeUIntLE 2 bytes
  let (firstTradeDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 2 bytes
  let (firstNoticeDate, bytes) ← decodeUIntLE 2 bytes
  let (lastNoticeDate, bytes) ← decodeUIntLE 2 bytes
  let (firstDeliveryDate, bytes) ← decodeUIntLE 2 bytes
  let (lastDeliveryDate, bytes) ← decodeUIntLE 2 bytes
  let (optionStrikePrice, bytes) ← decodeUIntLE 8 bytes
  let (optionStrikeCurrency, bytes) ← OptionStrikeCurrency.decode bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (optionExpirationType, bytes) ← OptionExpirationType.decode bytes
  let (underlyingFutureInstrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, instrumentId, underlyingAssetType, underlyingAssetAlphanumeric4, productGroupCodeAlphanumeric6, exchange, instrumentIdSource, instrumentType, instrumentListingStatus, reserved3, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, settlementPrice, settlementPriceTypeCalcMethod, totalVolume, openInterestQuantity, highLimitPrice, lowLimitPrice, tradingCollarVariationType, tradingCollarVariation, contractDate, maturityDate, valuationDate, firstTradeDate, lastTradeDate, firstNoticeDate, lastNoticeDate, firstDeliveryDate, lastDeliveryDate, optionStrikePrice, optionStrikeCurrency, optionType, optionExpirationType, underlyingFutureInstrumentId }, bytes)

@[simp] theorem encode_length (message : SimpleInstrumentDefinitionMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, UnderlyingAssetType.encode_length, Alpha.encode_length, InstrumentIdSource.encode_length, InstrumentType.encode_length, InstrumentListingStatus.encode_length, Currency.encode_length, SettlementCurrency.encode_length, MatchAlgorithm.encode_length, SettlementPriceTypeCalcMethod.encode_length, TradingCollarVariationType.encode_length, OptionStrikeCurrency.encode_length, OptionType.encode_length, OptionExpirationType.encode_length]

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
  rw [List.append_assoc, InstrumentListingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, OptionStrikeCurrency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionExpirationType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleInstrumentDefinitionMessage

/-- Instrument Leg: 42 bytes -/
structure InstrumentLeg where
  instrumentId : BitVec 32
  legRatioAndSide : BitVec 32
  maturityDate : BitVec 16
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace InstrumentLeg

def encode (message : InstrumentLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.legRatioAndSide
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (Alpha.encode message.reserved32)))

def decode (bytes : List UInt8) : Option (InstrumentLeg × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioAndSide, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ instrumentId, legRatioAndSide, maturityDate, reserved32 }, bytes)

@[simp] theorem encode_length (message : InstrumentLeg) : (encode message).length = 42 := by
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
  underlyingAssetAlphanumeric9 : Alpha 9
  productGroupCodeAlphanumeric13 : Alpha 13
  spreadType : SpreadType
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
  settlementPrice : BitVec 64
  settlementPriceTypeCalcMethod : SettlementPriceTypeCalcMethod
  tradingCollarVariationType : TradingCollarVariationType
  tradingCollarVariation : BitVec 64
  instrumentListingStatus : InstrumentListingStatus
  firstTradeDate : BitVec 16
  reserved64 : Alpha 64
  instrumentLeg : Bounded 1 InstrumentLeg
  deriving DecidableEq, Repr

namespace ComplexInstrumentDefinitionMessage

def encode (message : ComplexInstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (UnderlyingAssetType.encode message.underlyingAssetType
    ++ (Alpha.encode message.underlyingAssetAlphanumeric9
    ++ (Alpha.encode message.productGroupCodeAlphanumeric13
    ++ (SpreadType.encode message.spreadType
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
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (SettlementPriceTypeCalcMethod.encode message.settlementPriceTypeCalcMethod
    ++ (TradingCollarVariationType.encode message.tradingCollarVariationType
    ++ (encodeUIntLE 8 message.tradingCollarVariation
    ++ (InstrumentListingStatus.encode message.instrumentListingStatus
    ++ (encodeUIntLE 2 message.firstTradeDate
    ++ (Alpha.encode message.reserved64
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.instrumentLeg.val.length)
    ++ (encodeMany InstrumentLeg.encode message.instrumentLeg.val)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ComplexInstrumentDefinitionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingAssetType, bytes) ← UnderlyingAssetType.decode bytes
  let (underlyingAssetAlphanumeric9, bytes) ← Alpha.decode 9 bytes
  let (productGroupCodeAlphanumeric13, bytes) ← Alpha.decode 13 bytes
  let (spreadType, bytes) ← SpreadType.decode bytes
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
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPriceTypeCalcMethod, bytes) ← SettlementPriceTypeCalcMethod.decode bytes
  let (tradingCollarVariationType, bytes) ← TradingCollarVariationType.decode bytes
  let (tradingCollarVariation, bytes) ← decodeUIntLE 8 bytes
  let (instrumentListingStatus, bytes) ← InstrumentListingStatus.decode bytes
  let (firstTradeDate, bytes) ← decodeUIntLE 2 bytes
  let (reserved64, bytes) ← Alpha.decode 64 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (instrumentLeg_, bytes) ← decodeMany InstrumentLeg.decode numberOfLegs.toNat bytes
  if fits_instrumentLeg : instrumentLeg_.length < 256 ^ 1 then
    pure ({ timestamp, instrumentId, underlyingAssetType, underlyingAssetAlphanumeric9, productGroupCodeAlphanumeric13, spreadType, exchange, instrumentIdSource, instrumentType, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, settlementPrice, settlementPriceTypeCalcMethod, tradingCollarVariationType, tradingCollarVariation, instrumentListingStatus, firstTradeDate, reserved64, instrumentLeg := ⟨instrumentLeg_, fits_instrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexInstrumentDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexInstrumentDefinitionMessage) : (encode message).length ≤ 10866 := by
  have bound_instrumentLeg := message.instrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnderlyingAssetType.encode_length, Alpha.encode_length, SpreadType.encode_length, InstrumentIdSource.encode_length, InstrumentType.encode_length, Currency.encode_length, SettlementCurrency.encode_length, MatchAlgorithm.encode_length, SettlementPriceTypeCalcMethod.encode_length, TradingCollarVariationType.encode_length, InstrumentListingStatus.encode_length, encodeMany_length_const InstrumentLeg.encode 42 InstrumentLeg.encode_length]
  omega

set_option maxRecDepth 4096 in
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
  rw [List.append_assoc, SpreadType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceTypeCalcMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingCollarVariationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentListingStatus.decode_encode, some_bind]
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

/-- Deprecated Instrument Leg: 20 bytes -/
structure DeprecatedInstrumentLeg where
  instrumentId : BitVec 32
  legRatioAndSide : BitVec 32
  reserved4 : Alpha 4
  maturityDate : BitVec 16
  reserved6 : Alpha 6
  deriving DecidableEq, Repr

namespace DeprecatedInstrumentLeg

def encode (message : DeprecatedInstrumentLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.legRatioAndSide
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (Alpha.encode message.reserved6))))

def decode (bytes : List UInt8) : Option (DeprecatedInstrumentLeg × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioAndSide, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (reserved6, bytes) ← Alpha.decode 6 bytes
  pure ({ instrumentId, legRatioAndSide, reserved4, maturityDate, reserved6 }, bytes)

@[simp] theorem encode_length (message : DeprecatedInstrumentLeg) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DeprecatedInstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeprecatedInstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeprecatedInstrumentLeg

/-- Complex Instrument Definition Deprecated Message -/
structure ComplexInstrumentDefinitionDeprecatedMessage where
  timestamp : BitVec 64
  instrumentIdFormerlyKnownAsStrategyId : BitVec 32
  underlyingAssetType : UnderlyingAssetType
  underlyingAssetAlphanumeric4 : Alpha 4
  productGroupCodeAlphanumeric6 : Alpha 6
  spreadType : SpreadType
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
  deprecatedInstrumentLeg : Bounded 1 DeprecatedInstrumentLeg
  deriving DecidableEq, Repr

namespace ComplexInstrumentDefinitionDeprecatedMessage

def encode (message : ComplexInstrumentDefinitionDeprecatedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentIdFormerlyKnownAsStrategyId
    ++ (UnderlyingAssetType.encode message.underlyingAssetType
    ++ (Alpha.encode message.underlyingAssetAlphanumeric4
    ++ (Alpha.encode message.productGroupCodeAlphanumeric6
    ++ (SpreadType.encode message.spreadType
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
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.deprecatedInstrumentLeg.val.length)
    ++ (encodeMany DeprecatedInstrumentLeg.encode message.deprecatedInstrumentLeg.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexInstrumentDefinitionDeprecatedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentIdFormerlyKnownAsStrategyId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingAssetType, bytes) ← UnderlyingAssetType.decode bytes
  let (underlyingAssetAlphanumeric4, bytes) ← Alpha.decode 4 bytes
  let (productGroupCodeAlphanumeric6, bytes) ← Alpha.decode 6 bytes
  let (spreadType, bytes) ← SpreadType.decode bytes
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
  let (deprecatedInstrumentLeg_, bytes) ← decodeMany DeprecatedInstrumentLeg.decode numberOfLegs.toNat bytes
  if fits_deprecatedInstrumentLeg : deprecatedInstrumentLeg_.length < 256 ^ 1 then
    pure ({ timestamp, instrumentIdFormerlyKnownAsStrategyId, underlyingAssetType, underlyingAssetAlphanumeric4, productGroupCodeAlphanumeric6, spreadType, exchange, instrumentIdSource, instrumentType, currency, settlementCurrency, matchAlgorithm, minimumSize, maximumSize, tick, unitOfMeasure, unitOfMeasureQuantity, tradingCollarVariationType, tradingCollarVariation, reserved16, deprecatedInstrumentLeg := ⟨deprecatedInstrumentLeg_, fits_deprecatedInstrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexInstrumentDefinitionDeprecatedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexInstrumentDefinitionDeprecatedMessage) : (encode message).length ≤ 5184 := by
  have bound_deprecatedInstrumentLeg := message.deprecatedInstrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnderlyingAssetType.encode_length, Alpha.encode_length, SpreadType.encode_length, InstrumentIdSource.encode_length, InstrumentType.encode_length, Currency.encode_length, SettlementCurrency.encode_length, MatchAlgorithm.encode_length, TradingCollarVariationType.encode_length, encodeMany_length_const DeprecatedInstrumentLeg.encode 20 DeprecatedInstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexInstrumentDefinitionDeprecatedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SpreadType.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 DeprecatedInstrumentLeg.encode DeprecatedInstrumentLeg.decode DeprecatedInstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.deprecatedInstrumentLeg.length_lt]
  rfl

end ComplexInstrumentDefinitionDeprecatedMessage

/-- System State Message: 18 bytes -/
structure SystemStateMessage where
  timestamp : BitVec 64
  doMVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.doMVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (doMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ timestamp, doMVersion, sessionId, systemStatus }, bytes)

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

/-- Anticipated Opening Price Message: 25 bytes -/
structure AnticipatedOpeningPriceMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  anticipatedOpeningPrice : BitVec 64
  openingMatchQuantity : BitVec 32
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace AnticipatedOpeningPriceMessage

def encode (message : AnticipatedOpeningPriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.anticipatedOpeningPrice
    ++ (encodeUIntLE 4 message.openingMatchQuantity
    ++ (InstrumentType.encode message.instrumentType))))

def decode (bytes : List UInt8) : Option (AnticipatedOpeningPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (anticipatedOpeningPrice, bytes) ← decodeUIntLE 8 bytes
  let (openingMatchQuantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, instrumentId, anticipatedOpeningPrice, openingMatchQuantity, instrumentType }, bytes)

@[simp] theorem encode_length (message : AnticipatedOpeningPriceMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
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

/-- Add Order Message: 35 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderType : OrderType
  orderId : BitVec 64
  orderSide : OrderSide
  price : BitVec 64
  size : BitVec 32
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 8 message.orderId
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (InstrumentType.encode message.instrumentType)))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, instrumentId, orderType, orderId, orderSide, price, size, instrumentType }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderType.encode_length, OrderSide.encode_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Modify Order Message: 34 bytes -/
structure ModifyOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  sizeFlags : BitVec 32
  orderSide : OrderSide
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.sizeFlags
    ++ (OrderSide.encode message.orderSide
    ++ (InstrumentType.encode message.instrumentType))))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (sizeFlags, bytes) ← decodeUIntLE 4 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, instrumentId, orderId, price, sizeFlags, orderSide, instrumentType }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderSide.encode_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end ModifyOrderMessage

/-- Delete Order Message: 22 bytes -/
structure DeleteOrderMessage where
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  orderSide : OrderSide
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (OrderSide.encode message.orderSide
    ++ (InstrumentType.encode message.instrumentType))))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, instrumentId, orderId, orderSide, instrumentType }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderSide.encode_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end DeleteOrderMessage

/-- Order Execution Message: 62 bytes -/
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
  tradeType : TradeType
  complexTradeId : BitVec 64
  instrumentType : InstrumentType
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
    ++ (encodeUIntLE 4 message.size
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.complexTradeId
    ++ (InstrumentType.encode message.instrumentType))))))))))))

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
  let (tradeType, bytes) ← TradeType.decode bytes
  let (complexTradeId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, tradeDate, instrumentId, buyOrderId, sellOrderId, aggressorSide, tradeId, correctionNumber, price, size, tradeType, complexTradeId, instrumentType }, bytes)

@[simp] theorem encode_length (message : OrderExecutionMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AggressorSide.encode_length, TradeType.encode_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end OrderExecutionMessage

/-- Trade Cancel Message: 36 bytes -/
structure TradeCancelMessage where
  timestamp : BitVec 64
  tradeDate : BitVec 16
  instrumentId : BitVec 32
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (InstrumentType.encode message.instrumentType)))))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ timestamp, tradeDate, instrumentId, tradeId, correctionNumber, price, size, instrumentType }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentType.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end TradeCancelMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | simpleInstrumentDefinitionMessage (message : SimpleInstrumentDefinitionMessage) -- 1
  | complexInstrumentDefinitionMessage (message : ComplexInstrumentDefinitionMessage) -- 17
  | complexInstrumentDefinitionDeprecatedMessage (message : ComplexInstrumentDefinitionDeprecatedMessage) -- 2
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
  | .complexInstrumentDefinitionMessage _ => 17
  | .complexInstrumentDefinitionDeprecatedMessage _ => 2
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
  | .complexInstrumentDefinitionDeprecatedMessage message => ComplexInstrumentDefinitionDeprecatedMessage.encode message
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
theorem encode_length_le (message : Data) : (encode message).length ≤ 10866 := by
  cases message with
  | simpleInstrumentDefinitionMessage inner =>
    simp only [encode, SimpleInstrumentDefinitionMessage.encode_length]
    omega
  | complexInstrumentDefinitionMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | complexInstrumentDefinitionDeprecatedMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionDeprecatedMessage.encode_length_le inner
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
  else if tag = 17 then (ComplexInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDefinitionMessage message, rest)
  else if tag = 2 then (ComplexInstrumentDefinitionDeprecatedMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDefinitionDeprecatedMessage message, rest)
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
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 10867 := by
  unfold encode
  cases message.data with
  | simpleInstrumentDefinitionMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleInstrumentDefinitionMessage.encode_length]
    omega
  | complexInstrumentDefinitionMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, encodeUInt_length]
    omega
  | complexInstrumentDefinitionDeprecatedMessage inner =>
    have bound_inner := ComplexInstrumentDefinitionDeprecatedMessage.encode_length_le inner
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
theorem encode_length_le (message : Payload) : (encode message).length ≤ 10867 := by
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

end Omi.MiaxOnyxfuturesDepthofmarketMachV13A
