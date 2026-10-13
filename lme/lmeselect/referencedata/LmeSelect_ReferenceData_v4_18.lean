import Wire

/-!
# The London Metal Exchange LMEsource ReferenceData v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectReferencedataLmesourceV418

/-- Contract Type: one byte code -/
def ContractType.codes : List UInt8 :=
  [0x46, 0x4F]

inductive ContractType where
  | future -- Future
  | option -- Option
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractType

def toByte : ContractType → UInt8
  | .future => 0x46
  | .option => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractType :=
  if byte = 0x46 then .future
  else .option

def ofByte (byte : UInt8) : ContractType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractType) : ofByte value.toByte = value := by
  cases value with
  | future => decide
  | option => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContractType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContractType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractType

/-- Underlying Type: one byte code -/
def UnderlyingType.codes : List UInt8 :=
  [0x43, 0x46]

inductive UnderlyingType where
  | commodity -- Commodity
  | future -- Future
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingType

def toByte : UnderlyingType → UInt8
  | .commodity => 0x43
  | .future => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingType :=
  if byte = 0x43 then .commodity
  else .future

def ofByte (byte : UInt8) : UnderlyingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingType) : ofByte value.toByte = value := by
  cases value with
  | commodity => decide
  | future => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingType

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x43, 0x50]

inductive SettlementType where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Settlement Pricing Method: one byte code -/
def SettlementPricingMethod.codes : List UInt8 :=
  [0x44, 0x4D]

inductive SettlementPricingMethod where
  | daily -- Daily
  | monthlyAverage -- Monthly Average
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementPricingMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementPricingMethod

def toByte : SettlementPricingMethod → UInt8
  | .daily => 0x44
  | .monthlyAverage => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementPricingMethod :=
  if byte = 0x44 then .daily
  else .monthlyAverage

def ofByte (byte : UInt8) : SettlementPricingMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementPricingMethod) : ofByte value.toByte = value := by
  cases value with
  | daily => decide
  | monthlyAverage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementPricingMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementPricingMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementPricingMethod) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementPricingMethod) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementPricingMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementPricingMethod

/-- Lot Size Type: one byte code -/
def LotSizeType.codes : List UInt8 :=
  [0x53, 0x4D]

inductive LotSizeType where
  | standard -- Standard
  | mini -- Mini
  | unlisted (byte : { byte : UInt8 // byte ∉ LotSizeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LotSizeType

def toByte : LotSizeType → UInt8
  | .standard => 0x53
  | .mini => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LotSizeType :=
  if byte = 0x53 then .standard
  else .mini

def ofByte (byte : UInt8) : LotSizeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LotSizeType) : ofByte value.toByte = value := by
  cases value with
  | standard => decide
  | mini => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LotSizeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LotSizeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LotSizeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LotSizeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LotSizeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LotSizeType

/-- Contract Price Type: one byte code -/
def ContractPriceType.codes : List UInt8 :=
  [0x50, 0x56, 0x20]

inductive ContractPriceType where
  | premium -- Premium
  | volatility -- Volatility
  | futures -- Futures
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractPriceType

def toByte : ContractPriceType → UInt8
  | .premium => 0x50
  | .volatility => 0x56
  | .futures => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractPriceType :=
  if byte = 0x50 then .premium
  else if byte = 0x56 then .volatility
  else .futures

def ofByte (byte : UInt8) : ContractPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractPriceType) : ofByte value.toByte = value := by
  cases value with
  | premium => decide
  | volatility => decide
  | futures => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractPriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContractPriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContractPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractPriceType

/-- Prompt Type: one byte code -/
def PromptType.codes : List UInt8 :=
  [0x53, 0x52]

inductive PromptType where
  | single -- Single
  | rolling -- Rolling
  | unlisted (byte : { byte : UInt8 // byte ∉ PromptType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PromptType

def toByte : PromptType → UInt8
  | .single => 0x53
  | .rolling => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PromptType :=
  if byte = 0x53 then .single
  else .rolling

def ofByte (byte : UInt8) : PromptType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PromptType) : ofByte value.toByte = value := by
  cases value with
  | single => decide
  | rolling => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PromptType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PromptType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PromptType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PromptType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PromptType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PromptType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

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

theorem encode_length_pos (value : LegBuySell) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegBuySell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegBuySell

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Contract Definition Message: 134 bytes -/
structure ContractDefinitionMessage where
  tradingVenue : Alpha 2
  contractCode : Alpha 12
  name : Alpha 64
  contractType : ContractType
  productCode : Alpha 2
  underlyingType : UnderlyingType
  underlyingContractCode : Alpha 12
  tradingCurrency : Alpha 3
  settlementType : SettlementType
  settlementPricingMethod : SettlementPricingMethod
  exerciseStyle : BitVec 8
  lotUnit : Alpha 20
  lotSize : BitVec 64
  lotSizeType : LotSizeType
  contractPriceType : ContractPriceType
  firstTradingDate : BitVec 32
  deriving DecidableEq, Repr

namespace ContractDefinitionMessage

def encode (message : ContractDefinitionMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (Alpha.encode message.contractCode
    ++ (Alpha.encode message.name
    ++ (ContractType.encode message.contractType
    ++ (Alpha.encode message.productCode
    ++ (UnderlyingType.encode message.underlyingType
    ++ (Alpha.encode message.underlyingContractCode
    ++ (Alpha.encode message.tradingCurrency
    ++ (SettlementType.encode message.settlementType
    ++ (SettlementPricingMethod.encode message.settlementPricingMethod
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (Alpha.encode message.lotUnit
    ++ (encodeUIntLE 8 message.lotSize
    ++ (LotSizeType.encode message.lotSizeType
    ++ (ContractPriceType.encode message.contractPriceType
    ++ (encodeUIntLE 4 message.firstTradingDate)))))))))))))))

def decode (bytes : List UInt8) : Option (ContractDefinitionMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (name, bytes) ← Alpha.decode 64 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (underlyingContractCode, bytes) ← Alpha.decode 12 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlementPricingMethod, bytes) ← SettlementPricingMethod.decode bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (lotUnit, bytes) ← Alpha.decode 20 bytes
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeType, bytes) ← LotSizeType.decode bytes
  let (contractPriceType, bytes) ← ContractPriceType.decode bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ tradingVenue, contractCode, name, contractType, productCode, underlyingType, underlyingContractCode, tradingCurrency, settlementType, settlementPricingMethod, exerciseStyle, lotUnit, lotSize, lotSizeType, contractPriceType, firstTradingDate }, bytes)

@[simp] theorem encode_length (message : ContractDefinitionMessage) : (encode message).length = 134 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ContractType.encode_length, UnderlyingType.encode_length, SettlementType.encode_length, SettlementPricingMethod.encode_length, encodeUInt_length, encodeUIntLE_length, LotSizeType.encode_length, ContractPriceType.encode_length]

theorem encode_length_pos (message : ContractDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPricingMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractPriceType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ContractDefinitionMessage

/-- Outright Definition Message: 121 bytes -/
structure OutrightDefinitionMessage where
  tradingVenue : Alpha 2
  tradableInstrumentId : BitVec 64
  mergedTradableInstrumentId : BitVec 64
  linkedTradableInstrumentId : BitVec 64
  productCode : Alpha 2
  contractType : ContractType
  tradingCurrency : Alpha 3
  contractCode : Alpha 12
  expiryDate : BitVec 32
  promptType : PromptType
  strikePrice : BitVec 64
  optionType : OptionType
  exerciseStyle : BitVec 8
  promptDateLabel : Alpha 6
  priceCode : Alpha 2
  isin : Alpha 12
  cfiCode : Alpha 6
  marketCode : Alpha 4
  marketSegmentCode : Alpha 12
  tickSizeId : BitVec 32
  lotSize : BitVec 64
  lotSizeType : LotSizeType
  lastTradingDate : BitVec 32
  settlementType : SettlementType
  settlementPricingMethod : SettlementPricingMethod
  underlyingType : UnderlyingType
  deriving DecidableEq, Repr

namespace OutrightDefinitionMessage

def encode (message : OutrightDefinitionMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.mergedTradableInstrumentId
    ++ (encodeUIntLE 8 message.linkedTradableInstrumentId
    ++ (Alpha.encode message.productCode
    ++ (ContractType.encode message.contractType
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.contractCode
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (PromptType.encode message.promptType
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (Alpha.encode message.promptDateLabel
    ++ (Alpha.encode message.priceCode
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketSegmentCode
    ++ (encodeUIntLE 4 message.tickSizeId
    ++ (encodeUIntLE 8 message.lotSize
    ++ (LotSizeType.encode message.lotSizeType
    ++ (encodeUIntLE 4 message.lastTradingDate
    ++ (SettlementType.encode message.settlementType
    ++ (SettlementPricingMethod.encode message.settlementPricingMethod
    ++ (UnderlyingType.encode message.underlyingType)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OutrightDefinitionMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (mergedTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (linkedTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (promptType, bytes) ← PromptType.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (promptDateLabel, bytes) ← Alpha.decode 6 bytes
  let (priceCode, bytes) ← Alpha.decode 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentCode, bytes) ← Alpha.decode 12 bytes
  let (tickSizeId, bytes) ← decodeUIntLE 4 bytes
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeType, bytes) ← LotSizeType.decode bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlementPricingMethod, bytes) ← SettlementPricingMethod.decode bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  pure ({ tradingVenue, tradableInstrumentId, mergedTradableInstrumentId, linkedTradableInstrumentId, productCode, contractType, tradingCurrency, contractCode, expiryDate, promptType, strikePrice, optionType, exerciseStyle, promptDateLabel, priceCode, isin, cfiCode, marketCode, marketSegmentCode, tickSizeId, lotSize, lotSizeType, lastTradingDate, settlementType, settlementPricingMethod, underlyingType }, bytes)

@[simp] theorem encode_length (message : OutrightDefinitionMessage) : (encode message).length = 121 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, ContractType.encode_length, PromptType.encode_length, OptionType.encode_length, encodeUInt_length, LotSizeType.encode_length, SettlementType.encode_length, SettlementPricingMethod.encode_length, UnderlyingType.encode_length]

theorem encode_length_pos (message : OutrightDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OutrightDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PromptType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, LotSizeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPricingMethod.decode_encode, some_bind]
  dsimp only
  rw [UnderlyingType.decode_encode, some_bind]
  rfl

end OutrightDefinitionMessage

/-- Strategy Legs: 29 bytes -/
structure StrategyLegs where
  legNumber : BitVec 32
  legBuySell : LegBuySell
  legRatio : BitVec 64
  legDeltaHedgePrice : BitVec 64
  legTradableInstrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace StrategyLegs

def encode (message : StrategyLegs) : List UInt8 :=
  encodeUIntLE 4 message.legNumber
    ++ (LegBuySell.encode message.legBuySell
    ++ (encodeUIntLE 8 message.legRatio
    ++ (encodeUIntLE 8 message.legDeltaHedgePrice
    ++ (encodeUIntLE 8 message.legTradableInstrumentId))))

def decode (bytes : List UInt8) : Option (StrategyLegs × List UInt8) := do
  let (legNumber, bytes) ← decodeUIntLE 4 bytes
  let (legBuySell, bytes) ← LegBuySell.decode bytes
  let (legRatio, bytes) ← decodeUIntLE 8 bytes
  let (legDeltaHedgePrice, bytes) ← decodeUIntLE 8 bytes
  let (legTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ legNumber, legBuySell, legRatio, legDeltaHedgePrice, legTradableInstrumentId }, bytes)

@[simp] theorem encode_length (message : StrategyLegs) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegBuySell.encode_length]

theorem encode_length_pos (message : StrategyLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegBuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StrategyLegs

/-- Strategy Definition Message -/
structure StrategyDefinitionMessage where
  tradingVenue : Alpha 2
  tradableInstrumentId : BitVec 64
  mergedTradableInstrumentId : BitVec 64
  productCode : Alpha 2
  contractType : ContractType
  tradingCurrency : Alpha 3
  strategyTypeCode : BitVec 32
  contractCode : Alpha 12
  exerciseStyle : BitVec 8
  priceCode : Alpha 2
  marketCode : Alpha 4
  marketSegmentCode : Alpha 12
  tickSizeId : BitVec 32
  lotSize : BitVec 64
  lotSizeType : LotSizeType
  lastTradingDate : BitVec 32
  settlementType : SettlementType
  settlementPricingMethod : SettlementPricingMethod
  underlyingType : UnderlyingType
  strategyLegs : Bounded 4 StrategyLegs
  deriving DecidableEq, Repr

namespace StrategyDefinitionMessage

def encode (message : StrategyDefinitionMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.mergedTradableInstrumentId
    ++ (Alpha.encode message.productCode
    ++ (ContractType.encode message.contractType
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUIntLE 4 message.strategyTypeCode
    ++ (Alpha.encode message.contractCode
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (Alpha.encode message.priceCode
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketSegmentCode
    ++ (encodeUIntLE 4 message.tickSizeId
    ++ (encodeUIntLE 8 message.lotSize
    ++ (LotSizeType.encode message.lotSizeType
    ++ (encodeUIntLE 4 message.lastTradingDate
    ++ (SettlementType.encode message.settlementType
    ++ (SettlementPricingMethod.encode message.settlementPricingMethod
    ++ (UnderlyingType.encode message.underlyingType
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.strategyLegs.val.length)
    ++ (encodeMany StrategyLegs.encode message.strategyLegs.val))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyDefinitionMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (mergedTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (strategyTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (priceCode, bytes) ← Alpha.decode 2 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentCode, bytes) ← Alpha.decode 12 bytes
  let (tickSizeId, bytes) ← decodeUIntLE 4 bytes
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeType, bytes) ← LotSizeType.decode bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlementPricingMethod, bytes) ← SettlementPricingMethod.decode bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (strategyLegCount, bytes) ← decodeUIntLE 4 bytes
  let (strategyLegs_, bytes) ← decodeMany StrategyLegs.decode strategyLegCount.toNat bytes
  if fits_strategyLegs : strategyLegs_.length < 256 ^ 4 then
    pure ({ tradingVenue, tradableInstrumentId, mergedTradableInstrumentId, productCode, contractType, tradingCurrency, strategyTypeCode, contractCode, exerciseStyle, priceCode, marketCode, marketSegmentCode, tickSizeId, lotSize, lotSizeType, lastTradingDate, settlementType, settlementPricingMethod, underlyingType, strategyLegs := ⟨strategyLegs_, fits_strategyLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyDefinitionMessage) : (encode message).length ≤ 124554051638 := by
  have bound_strategyLegs := message.strategyLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUIntLE_length, ContractType.encode_length, encodeUInt_length, LotSizeType.encode_length, SettlementType.encode_length, SettlementPricingMethod.encode_length, UnderlyingType.encode_length, encodeMany_length_const StrategyLegs.encode 29 StrategyLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPricingMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 StrategyLegs.encode StrategyLegs.decode StrategyLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyLegs.length_lt]
  rfl

end StrategyDefinitionMessage

/-- Price Limits Message: 32 bytes -/
structure PriceLimitsMessage where
  tradableInstrumentId : BitVec 64
  upperPriceLimit : BitVec 64
  lowerPriceLimit : BitVec 64
  transactionTime : BitVec 64
  deriving DecidableEq, Repr

namespace PriceLimitsMessage

def encode (message : PriceLimitsMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.upperPriceLimit
    ++ (encodeUIntLE 8 message.lowerPriceLimit
    ++ (encodeUIntLE 8 message.transactionTime)))

def decode (bytes : List UInt8) : Option (PriceLimitsMessage × List UInt8) := do
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (upperPriceLimit, bytes) ← decodeUIntLE 8 bytes
  let (lowerPriceLimit, bytes) ← decodeUIntLE 8 bytes
  let (transactionTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradableInstrumentId, upperPriceLimit, lowerPriceLimit, transactionTime }, bytes)

@[simp] theorem encode_length (message : PriceLimitsMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : PriceLimitsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLimitsMessage) (rest : List UInt8) :
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

end PriceLimitsMessage

/-- Trade Statistics End Of Day Message: 50 bytes -/
structure TradeStatisticsEndOfDayMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  openPrice : BitVec 64
  tradeHigh : BitVec 64
  tradeLow : BitVec 64
  closingPrice : BitVec 64
  deriving DecidableEq, Repr

namespace TradeStatisticsEndOfDayMessage

def encode (message : TradeStatisticsEndOfDayMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.openPrice
    ++ (encodeUIntLE 8 message.tradeHigh
    ++ (encodeUIntLE 8 message.tradeLow
    ++ (encodeUIntLE 8 message.closingPrice))))))

def decode (bytes : List UInt8) : Option (TradeStatisticsEndOfDayMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (openPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeHigh, bytes) ← decodeUIntLE 8 bytes
  let (tradeLow, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, openPrice, tradeHigh, tradeLow, closingPrice }, bytes)

@[simp] theorem encode_length (message : TradeStatisticsEndOfDayMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeStatisticsEndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeStatisticsEndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeStatisticsEndOfDayMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | contractDefinitionMessage (message : ContractDefinitionMessage) -- 300
  | outrightDefinitionMessage (message : OutrightDefinitionMessage) -- 301
  | strategyDefinitionMessage (message : StrategyDefinitionMessage) -- 302
  | priceLimitsMessage (message : PriceLimitsMessage) -- 305
  | tradeStatisticsEndOfDayMessage (message : TradeStatisticsEndOfDayMessage) -- 351
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .contractDefinitionMessage _ => 300
  | .outrightDefinitionMessage _ => 301
  | .strategyDefinitionMessage _ => 302
  | .priceLimitsMessage _ => 305
  | .tradeStatisticsEndOfDayMessage _ => 351

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .contractDefinitionMessage message => ContractDefinitionMessage.encode message
  | .outrightDefinitionMessage message => OutrightDefinitionMessage.encode message
  | .strategyDefinitionMessage message => StrategyDefinitionMessage.encode message
  | .priceLimitsMessage message => PriceLimitsMessage.encode message
  | .tradeStatisticsEndOfDayMessage message => TradeStatisticsEndOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 124554051638 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | contractDefinitionMessage inner =>
    simp only [encode, ContractDefinitionMessage.encode_length]
    omega
  | outrightDefinitionMessage inner =>
    simp only [encode, OutrightDefinitionMessage.encode_length]
    omega
  | strategyDefinitionMessage inner =>
    have bound_inner := StrategyDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | priceLimitsMessage inner =>
    simp only [encode, PriceLimitsMessage.encode_length]
    omega
  | tradeStatisticsEndOfDayMessage inner =>
    simp only [encode, TradeStatisticsEndOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 300 then (ContractDefinitionMessage.decode bytes).map fun (message, rest) => (.contractDefinitionMessage message, rest)
  else if tag = 301 then (OutrightDefinitionMessage.decode bytes).map fun (message, rest) => (.outrightDefinitionMessage message, rest)
  else if tag = 302 then (StrategyDefinitionMessage.decode bytes).map fun (message, rest) => (.strategyDefinitionMessage message, rest)
  else if tag = 305 then (PriceLimitsMessage.decode bytes).map fun (message, rest) => (.priceLimitsMessage message, rest)
  else if tag = 351 then (TradeStatisticsEndOfDayMessage.decode bytes).map fun (message, rest) => (.tradeStatisticsEndOfDayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Messages -/
structure Messages where
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Messages

def encode (message : Messages) : List UInt8 :=
  encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Messages × List UInt8) := do
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSize, payload }, bytes)

theorem encode_length_pos (message : Messages) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Messages) : (encode message).length ≤ 124554051642 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | contractDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ContractDefinitionMessage.encode_length]
    omega
  | outrightDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OutrightDefinitionMessage.encode_length]
    omega
  | strategyDefinitionMessage inner =>
    have bound_inner := StrategyDefinitionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | priceLimitsMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PriceLimitsMessage.encode_length]
    omega
  | tradeStatisticsEndOfDayMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeStatisticsEndOfDayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Messages) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Messages

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  messages : Bounded 1 Messages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messages.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Messages.encode message.messages.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (messages_, bytes) ← decodeMany Messages.decode msgCount.toNat bytes
  if fits_messages : messages_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, messages := ⟨messages_, fits_messages⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 31761283168726 := by
  have bound_messages := message.messages.length_lt
  have bound_messages_items := encodeMany_length_le Messages.encode 124554051642 Messages.encode_length_le message.messages.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeMany_bounded 1 Messages.encode Messages.decode Messages.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messages.length_lt]
  rfl

end Packet

end Omi.LmeLmeselectReferencedataLmesourceV418
