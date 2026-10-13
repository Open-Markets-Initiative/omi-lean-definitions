import Wire

/-!
# The London Metal Exchange LMEsource NonElectronicRefData v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectNonelectronicrefdataLmesourceV418

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

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x4F, 0x53]

inductive InstrumentType where
  | outright -- Outright
  | strategy -- Strategy
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .outright => 0x4F
  | .strategy => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x4F then .outright
  else .strategy

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | outright => decide
  | strategy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

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

/-- Instrument Definition Message: 99 bytes -/
structure InstrumentDefinitionMessage where
  instrumentId : BitVec 64
  name : Alpha 40
  contractCode : Alpha 12
  underlyingInstrumentId : BitVec 64
  expiryDate : BitVec 32
  strikePrice : BitVec 64
  optionType : OptionType
  cfiCode : Alpha 6
  isin : Alpha 12
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessage

def encode (message : InstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.name
    ++ (Alpha.encode message.contractCode
    ++ (encodeUIntLE 8 message.underlyingInstrumentId
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.isin))))))))

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (name, bytes) ← Alpha.decode 40 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  pure ({ instrumentId, name, contractCode, underlyingInstrumentId, expiryDate, strikePrice, optionType, cfiCode, isin }, bytes)

@[simp] theorem encode_length (message : InstrumentDefinitionMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OptionType.encode_length]

theorem encode_length_pos (message : InstrumentDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDefinitionMessage

/-- Definition Legs: 29 bytes -/
structure DefinitionLegs where
  legNumber : BitVec 32
  legBuySell : LegBuySell
  legRatio : BitVec 64
  legDeltaHedgePrice : BitVec 64
  legTradableInstrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace DefinitionLegs

def encode (message : DefinitionLegs) : List UInt8 :=
  encodeUIntLE 4 message.legNumber
    ++ (LegBuySell.encode message.legBuySell
    ++ (encodeUIntLE 8 message.legRatio
    ++ (encodeUIntLE 8 message.legDeltaHedgePrice
    ++ (encodeUIntLE 8 message.legTradableInstrumentId))))

def decode (bytes : List UInt8) : Option (DefinitionLegs × List UInt8) := do
  let (legNumber, bytes) ← decodeUIntLE 4 bytes
  let (legBuySell, bytes) ← LegBuySell.decode bytes
  let (legRatio, bytes) ← decodeUIntLE 8 bytes
  let (legDeltaHedgePrice, bytes) ← decodeUIntLE 8 bytes
  let (legTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ legNumber, legBuySell, legRatio, legDeltaHedgePrice, legTradableInstrumentId }, bytes)

@[simp] theorem encode_length (message : DefinitionLegs) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegBuySell.encode_length]

theorem encode_length_pos (message : DefinitionLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DefinitionLegs) (rest : List UInt8) :
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

end DefinitionLegs

/-- Tradable Instrument Definition Message -/
structure TradableInstrumentDefinitionMessage where
  tradableInstrumentId : BitVec 64
  instrumentId : BitVec 64
  tradingVenue : Alpha 2
  businessDaysToExpiry : BitVec 32
  lastTradingDate : BitVec 32
  tickSizeId : BitVec 32
  contractCode : Alpha 12
  contractType : ContractType
  instrumentType : InstrumentType
  tradingCurrency : Alpha 3
  marketCode : Alpha 4
  marketSegmentCode : Alpha 12
  productCode : Alpha 2
  underlyingTradableInstrumentId : BitVec 64
  settlementDate : BitVec 32
  expiryDate : BitVec 32
  optionType : OptionType
  strikePrice : BitVec 64
  cfiCode : Alpha 6
  isin : Alpha 12
  tradeAtReference : BitVec 8
  priceCode : Alpha 2
  promptDateLabel : Alpha 6
  promptType : PromptType
  optionStrikeRelativePosition : BitVec 32
  strategyTypeCode : BitVec 32
  remainingRecords : BitVec 16
  strategyLegCount : BitVec 32
  definitionLegs : Bounded 2 DefinitionLegs
  deriving DecidableEq, Repr

namespace TradableInstrumentDefinitionMessage

def encode (message : TradableInstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 4 message.businessDaysToExpiry
    ++ (encodeUIntLE 4 message.lastTradingDate
    ++ (encodeUIntLE 4 message.tickSizeId
    ++ (Alpha.encode message.contractCode
    ++ (ContractType.encode message.contractType
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketSegmentCode
    ++ (Alpha.encode message.productCode
    ++ (encodeUIntLE 8 message.underlyingTradableInstrumentId
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (OptionType.encode message.optionType
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.tradeAtReference
    ++ (Alpha.encode message.priceCode
    ++ (Alpha.encode message.promptDateLabel
    ++ (PromptType.encode message.promptType
    ++ (encodeUIntLE 4 message.optionStrikeRelativePosition
    ++ (encodeUIntLE 4 message.strategyTypeCode
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.definitionLegs.val.length)
    ++ (encodeUIntLE 4 message.strategyLegCount
    ++ (encodeMany DefinitionLegs.encode message.definitionLegs.val)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradableInstrumentDefinitionMessage × List UInt8) := do
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (businessDaysToExpiry, bytes) ← decodeUIntLE 4 bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (tickSizeId, bytes) ← decodeUIntLE 4 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentCode, bytes) ← Alpha.decode 12 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (underlyingTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (tradeAtReference, bytes) ← decodeUInt 1 bytes
  let (priceCode, bytes) ← Alpha.decode 2 bytes
  let (promptDateLabel, bytes) ← Alpha.decode 6 bytes
  let (promptType, bytes) ← PromptType.decode bytes
  let (optionStrikeRelativePosition, bytes) ← decodeUIntLE 4 bytes
  let (strategyTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (strategyLegCount, bytes) ← decodeUIntLE 4 bytes
  let (definitionLegs_, bytes) ← decodeMany DefinitionLegs.decode recordCount.toNat bytes
  if fits_definitionLegs : definitionLegs_.length < 256 ^ 2 then
    pure ({ tradableInstrumentId, instrumentId, tradingVenue, businessDaysToExpiry, lastTradingDate, tickSizeId, contractCode, contractType, instrumentType, tradingCurrency, marketCode, marketSegmentCode, productCode, underlyingTradableInstrumentId, settlementDate, expiryDate, optionType, strikePrice, cfiCode, isin, tradeAtReference, priceCode, promptDateLabel, promptType, optionStrikeRelativePosition, strategyTypeCode, remainingRecords, strategyLegCount, definitionLegs := ⟨definitionLegs_, fits_definitionLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradableInstrumentDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradableInstrumentDefinitionMessage) : (encode message).length ≤ 1900649 := by
  have bound_definitionLegs := message.definitionLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ContractType.encode_length, InstrumentType.encode_length, OptionType.encode_length, encodeUInt_length, PromptType.encode_length, encodeMany_length_const DefinitionLegs.encode 29 DefinitionLegs.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradableInstrumentDefinitionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, PromptType.decode_encode, some_bind]
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
  rw [decodeMany_bounded 2 DefinitionLegs.encode DefinitionLegs.decode DefinitionLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.definitionLegs.length_lt]
  rfl

end TradableInstrumentDefinitionMessage

/-- Order Statistics Intraday Message: 36 bytes -/
structure OrderStatisticsIntradayMessage where
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  tradingVenue : Alpha 2
  ringSession : Alpha 2
  orderHigh : BitVec 64
  orderLow : BitVec 64
  deriving DecidableEq, Repr

namespace OrderStatisticsIntradayMessage

def encode (message : OrderStatisticsIntradayMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (Alpha.encode message.tradingVenue
    ++ (Alpha.encode message.ringSession
    ++ (encodeUIntLE 8 message.orderHigh
    ++ (encodeUIntLE 8 message.orderLow)))))

def decode (bytes : List UInt8) : Option (OrderStatisticsIntradayMessage × List UInt8) := do
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (ringSession, bytes) ← Alpha.decode 2 bytes
  let (orderHigh, bytes) ← decodeUIntLE 8 bytes
  let (orderLow, bytes) ← decodeUIntLE 8 bytes
  pure ({ timeOfEvent, tradableInstrumentId, tradingVenue, ringSession, orderHigh, orderLow }, bytes)

@[simp] theorem encode_length (message : OrderStatisticsIntradayMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderStatisticsIntradayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderStatisticsIntradayMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderStatisticsIntradayMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | instrumentDefinitionMessage (message : InstrumentDefinitionMessage) -- 303
  | tradableInstrumentDefinitionMessage (message : TradableInstrumentDefinitionMessage) -- 304
  | orderStatisticsIntradayMessage (message : OrderStatisticsIntradayMessage) -- 350
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .instrumentDefinitionMessage _ => 303
  | .tradableInstrumentDefinitionMessage _ => 304
  | .orderStatisticsIntradayMessage _ => 350

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .instrumentDefinitionMessage message => InstrumentDefinitionMessage.encode message
  | .tradableInstrumentDefinitionMessage message => TradableInstrumentDefinitionMessage.encode message
  | .orderStatisticsIntradayMessage message => OrderStatisticsIntradayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1900649 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | instrumentDefinitionMessage inner =>
    simp only [encode, InstrumentDefinitionMessage.encode_length]
    omega
  | tradableInstrumentDefinitionMessage inner =>
    have bound_inner := TradableInstrumentDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderStatisticsIntradayMessage inner =>
    simp only [encode, OrderStatisticsIntradayMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 303 then (InstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.instrumentDefinitionMessage message, rest)
  else if tag = 304 then (TradableInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.tradableInstrumentDefinitionMessage message, rest)
  else if tag = 350 then (OrderStatisticsIntradayMessage.decode bytes).map fun (message, rest) => (.orderStatisticsIntradayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSize, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 1900653 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | instrumentDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentDefinitionMessage.encode_length]
    omega
  | tradableInstrumentDefinitionMessage inner =>
    have bound_inner := TradableInstrumentDefinitionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | orderStatisticsIntradayMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderStatisticsIntradayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 484666531 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 1900653 Message.encode_length_le message.message.val
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
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.LmeLmeselectNonelectronicrefdataLmesourceV418
