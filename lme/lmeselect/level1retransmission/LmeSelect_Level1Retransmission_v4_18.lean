import Wire

/-!
# The London Metal Exchange LMEsource Level1 Retransmission v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectLevel1retransmissionLmesourceV418

/-- Trading State Condition: one byte code -/
def TradingStateCondition.codes : List UInt8 :=
  [0x50, 0x48, 0x20]

inductive TradingStateCondition where
  | pause -- Pause
  | halt -- Halt
  | active -- Active
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStateCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStateCondition

def toByte : TradingStateCondition → UInt8
  | .pause => 0x50
  | .halt => 0x48
  | .active => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStateCondition :=
  if byte = 0x50 then .pause
  else if byte = 0x48 then .halt
  else .active

def ofByte (byte : UInt8) : TradingStateCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStateCondition) : ofByte value.toByte = value := by
  cases value with
  | pause => decide
  | halt => decide
  | active => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStateCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStateCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStateCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingStateCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingStateCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStateCondition

/-- Timetable Control Type: one byte code -/
def TimetableControlType.codes : List UInt8 :=
  [0x41, 0x4D]

inductive TimetableControlType where
  | automaticTheDefaultTradingSchedule -- Automatic The Default Trading Schedule
  | manualATemporaryTradingSchedule -- Manual A Temporary Trading Schedule
  | unlisted (byte : { byte : UInt8 // byte ∉ TimetableControlType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimetableControlType

def toByte : TimetableControlType → UInt8
  | .automaticTheDefaultTradingSchedule => 0x41
  | .manualATemporaryTradingSchedule => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimetableControlType :=
  if byte = 0x41 then .automaticTheDefaultTradingSchedule
  else .manualATemporaryTradingSchedule

def ofByte (byte : UInt8) : TimetableControlType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimetableControlType) : ofByte value.toByte = value := by
  cases value with
  | automaticTheDefaultTradingSchedule => decide
  | manualATemporaryTradingSchedule => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimetableControlType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimetableControlType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimetableControlType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TimetableControlType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TimetableControlType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimetableControlType

/-- Buy Sell: one byte code -/
def BuySell.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive BuySell where
  | buy -- Buy
  | sell -- Sell
  | twoSidedQuote -- Two Sided Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySell.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySell

def toByte : BuySell → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .twoSidedQuote => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySell :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .twoSidedQuote

def ofByte (byte : UInt8) : BuySell :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySell) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | twoSidedQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySell) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySell × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySell) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuySell) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuySell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySell

/-- Trade At Reference Price Type: one byte code -/
def TradeAtReferencePriceType.codes : List UInt8 :=
  [0x44, 0x53, 0x20]

inductive TradeAtReferencePriceType where
  | differential -- Differential
  | substituted -- Substituted
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeAtReferencePriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeAtReferencePriceType

def toByte : TradeAtReferencePriceType → UInt8
  | .differential => 0x44
  | .substituted => 0x53
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeAtReferencePriceType :=
  if byte = 0x44 then .differential
  else if byte = 0x53 then .substituted
  else .notApplicable

def ofByte (byte : UInt8) : TradeAtReferencePriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeAtReferencePriceType) : ofByte value.toByte = value := by
  cases value with
  | differential => decide
  | substituted => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeAtReferencePriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeAtReferencePriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeAtReferencePriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeAtReferencePriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeAtReferencePriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeAtReferencePriceType

/-- Leg Trade At Reference Price: one byte code -/
def LegTradeAtReferencePrice.codes : List UInt8 :=
  [0x44, 0x53, 0x20]

inductive LegTradeAtReferencePrice where
  | differential -- Differential
  | substituted -- Substituted
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LegTradeAtReferencePrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegTradeAtReferencePrice

def toByte : LegTradeAtReferencePrice → UInt8
  | .differential => 0x44
  | .substituted => 0x53
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegTradeAtReferencePrice :=
  if byte = 0x44 then .differential
  else if byte = 0x53 then .substituted
  else .notApplicable

def ofByte (byte : UInt8) : LegTradeAtReferencePrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegTradeAtReferencePrice) : ofByte value.toByte = value := by
  cases value with
  | differential => decide
  | substituted => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegTradeAtReferencePrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegTradeAtReferencePrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegTradeAtReferencePrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegTradeAtReferencePrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegTradeAtReferencePrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegTradeAtReferencePrice

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

/-- Market State Contract Message: 42 bytes -/
structure MarketStateContractMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  contractCode : Alpha 12
  tradingState : BitVec 8
  startTime : BitVec 64
  endTime : BitVec 64
  tradingStateCondition : TradingStateCondition
  fillerString2 : Alpha 2
  deriving DecidableEq, Repr

namespace MarketStateContractMessage

def encode (message : MarketStateContractMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (Alpha.encode message.contractCode
    ++ (encodeUInt 1 message.tradingState
    ++ (encodeUIntLE 8 message.startTime
    ++ (encodeUIntLE 8 message.endTime
    ++ (TradingStateCondition.encode message.tradingStateCondition
    ++ (Alpha.encode message.fillerString2)))))))

def decode (bytes : List UInt8) : Option (MarketStateContractMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (tradingState, bytes) ← decodeUInt 1 bytes
  let (startTime, bytes) ← decodeUIntLE 8 bytes
  let (endTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingStateCondition, bytes) ← TradingStateCondition.decode bytes
  let (fillerString2, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingVenue, timeOfEvent, contractCode, tradingState, startTime, endTime, tradingStateCondition, fillerString2 }, bytes)

@[simp] theorem encode_length (message : MarketStateContractMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, TradingStateCondition.encode_length]

theorem encode_length_pos (message : MarketStateContractMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateContractMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStateCondition.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketStateContractMessage

/-- Market State Instrument Message: 40 bytes -/
structure MarketStateInstrumentMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  timetableControlType : TimetableControlType
  tradingState : BitVec 8
  startTime : BitVec 64
  endTime : BitVec 64
  tradingStateCondition : TradingStateCondition
  fillerString3 : Alpha 3
  deriving DecidableEq, Repr

namespace MarketStateInstrumentMessage

def encode (message : MarketStateInstrumentMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (TimetableControlType.encode message.timetableControlType
    ++ (encodeUInt 1 message.tradingState
    ++ (encodeUIntLE 8 message.startTime
    ++ (encodeUIntLE 8 message.endTime
    ++ (TradingStateCondition.encode message.tradingStateCondition
    ++ (Alpha.encode message.fillerString3))))))))

def decode (bytes : List UInt8) : Option (MarketStateInstrumentMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (timetableControlType, bytes) ← TimetableControlType.decode bytes
  let (tradingState, bytes) ← decodeUInt 1 bytes
  let (startTime, bytes) ← decodeUIntLE 8 bytes
  let (endTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingStateCondition, bytes) ← TradingStateCondition.decode bytes
  let (fillerString3, bytes) ← Alpha.decode 3 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, timetableControlType, tradingState, startTime, endTime, tradingStateCondition, fillerString3 }, bytes)

@[simp] theorem encode_length (message : MarketStateInstrumentMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, TimetableControlType.encode_length, encodeUInt_length, TradingStateCondition.encode_length]

theorem encode_length_pos (message : MarketStateInstrumentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateInstrumentMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimetableControlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStateCondition.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketStateInstrumentMessage

/-- Indicative Opening Price Message: 40 bytes -/
structure IndicativeOpeningPriceMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  indicativeOpeningPrice : BitVec 64
  indicativeOpeningVolume : BitVec 32
  indicativeOpeningMidPrice : BitVec 64
  fillerString2 : Alpha 2
  deriving DecidableEq, Repr

namespace IndicativeOpeningPriceMessage

def encode (message : IndicativeOpeningPriceMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.indicativeOpeningPrice
    ++ (encodeUIntLE 4 message.indicativeOpeningVolume
    ++ (encodeUIntLE 8 message.indicativeOpeningMidPrice
    ++ (Alpha.encode message.fillerString2))))))

def decode (bytes : List UInt8) : Option (IndicativeOpeningPriceMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (indicativeOpeningPrice, bytes) ← decodeUIntLE 8 bytes
  let (indicativeOpeningVolume, bytes) ← decodeUIntLE 4 bytes
  let (indicativeOpeningMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillerString2, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, indicativeOpeningPrice, indicativeOpeningVolume, indicativeOpeningMidPrice, fillerString2 }, bytes)

@[simp] theorem encode_length (message : IndicativeOpeningPriceMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : IndicativeOpeningPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativeOpeningPriceMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndicativeOpeningPriceMessage

/-- Quote Request Message: 26 bytes -/
structure QuoteRequestMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  quoteRequestType : BitVec 8
  buySell : BuySell
  volume : BitVec 32
  fillerString2 : Alpha 2
  deriving DecidableEq, Repr

namespace QuoteRequestMessage

def encode (message : QuoteRequestMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUInt 1 message.quoteRequestType
    ++ (BuySell.encode message.buySell
    ++ (encodeUIntLE 4 message.volume
    ++ (Alpha.encode message.fillerString2))))))

def decode (bytes : List UInt8) : Option (QuoteRequestMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quoteRequestType, bytes) ← decodeUInt 1 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (fillerString2, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, quoteRequestType, buySell, volume, fillerString2 }, bytes)

@[simp] theorem encode_length (message : QuoteRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, BuySell.encode_length]

theorem encode_length_pos (message : QuoteRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteRequestMessage

/-- Order Book Clear Message: 18 bytes -/
structure OrderBookClearMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Cross Request Message: 40 bytes -/
structure CrossRequestMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  crossId : BitVec 64
  volume : BitVec 32
  expireTime : BitVec 64
  fillerString2 : Alpha 2
  deriving DecidableEq, Repr

namespace CrossRequestMessage

def encode (message : CrossRequestMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.crossId
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.expireTime
    ++ (Alpha.encode message.fillerString2))))))

def decode (bytes : List UInt8) : Option (CrossRequestMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (crossId, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (fillerString2, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, crossId, volume, expireTime, fillerString2 }, bytes)

@[simp] theorem encode_length (message : CrossRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CrossRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequestMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossRequestMessage

/-- Top Of Book Message: 98 bytes -/
structure TopOfBookMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  aggregateBidVolume : BitVec 64
  aggregateAskVolume : BitVec 64
  bidPrice : BitVec 64
  askPrice : BitVec 64
  numberBidExplicitOrders : BitVec 32
  bidQtyExplicitOrders : BitVec 64
  numberAskExplicitOrders : BitVec 32
  askQtyExplicitOrders : BitVec 64
  numberBidImpliedOrders : BitVec 32
  bidQtyImpliedOrders : BitVec 64
  numberAskImpliedOrders : BitVec 32
  askQtyImpliedOrders : BitVec 64
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.aggregateBidVolume
    ++ (encodeUIntLE 8 message.aggregateAskVolume
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 8 message.askPrice
    ++ (encodeUIntLE 4 message.numberBidExplicitOrders
    ++ (encodeUIntLE 8 message.bidQtyExplicitOrders
    ++ (encodeUIntLE 4 message.numberAskExplicitOrders
    ++ (encodeUIntLE 8 message.askQtyExplicitOrders
    ++ (encodeUIntLE 4 message.numberBidImpliedOrders
    ++ (encodeUIntLE 8 message.bidQtyImpliedOrders
    ++ (encodeUIntLE 4 message.numberAskImpliedOrders
    ++ (encodeUIntLE 8 message.askQtyImpliedOrders))))))))))))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (aggregateBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (aggregateAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (numberBidExplicitOrders, bytes) ← decodeUIntLE 4 bytes
  let (bidQtyExplicitOrders, bytes) ← decodeUIntLE 8 bytes
  let (numberAskExplicitOrders, bytes) ← decodeUIntLE 4 bytes
  let (askQtyExplicitOrders, bytes) ← decodeUIntLE 8 bytes
  let (numberBidImpliedOrders, bytes) ← decodeUIntLE 4 bytes
  let (bidQtyImpliedOrders, bytes) ← decodeUIntLE 8 bytes
  let (numberAskImpliedOrders, bytes) ← decodeUIntLE 4 bytes
  let (askQtyImpliedOrders, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, aggregateBidVolume, aggregateAskVolume, bidPrice, askPrice, numberBidExplicitOrders, bidQtyExplicitOrders, numberAskExplicitOrders, askQtyExplicitOrders, numberBidImpliedOrders, bidQtyImpliedOrders, numberAskImpliedOrders, askQtyImpliedOrders }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
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

end TopOfBookMessage

/-- Trade Legs: 21 bytes -/
structure TradeLegs where
  legPrice : BitVec 64
  legVolume : BitVec 32
  legMatchId : BitVec 64
  legTradeAtReferencePrice : LegTradeAtReferencePrice
  deriving DecidableEq, Repr

namespace TradeLegs

def encode (message : TradeLegs) : List UInt8 :=
  encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legVolume
    ++ (encodeUIntLE 8 message.legMatchId
    ++ (LegTradeAtReferencePrice.encode message.legTradeAtReferencePrice)))

def decode (bytes : List UInt8) : Option (TradeLegs × List UInt8) := do
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legVolume, bytes) ← decodeUIntLE 4 bytes
  let (legMatchId, bytes) ← decodeUIntLE 8 bytes
  let (legTradeAtReferencePrice, bytes) ← LegTradeAtReferencePrice.decode bytes
  pure ({ legPrice, legVolume, legMatchId, legTradeAtReferencePrice }, bytes)

@[simp] theorem encode_length (message : TradeLegs) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegTradeAtReferencePrice.encode_length]

theorem encode_length_pos (message : TradeLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LegTradeAtReferencePrice.decode_encode, some_bind]
  rfl

end TradeLegs

/-- Market Data Trade Message -/
structure MarketDataTradeMessage where
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  tradingVenue : Alpha 2
  matchedTime : BitVec 64
  ringSession : Alpha 2
  tradeCancelFlag : BitVec 8
  price : BitVec 64
  volume : BitVec 32
  matchId : BitVec 64
  tradeAtReferencePriceType : TradeAtReferencePriceType
  subTypeOfTrade : BitVec 8
  remainingRecords : BitVec 16
  strategyLegCount : BitVec 32
  tradeLegs : Bounded 2 TradeLegs
  deriving DecidableEq, Repr

namespace MarketDataTradeMessage

def encode (message : MarketDataTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.matchedTime
    ++ (Alpha.encode message.ringSession
    ++ (encodeUInt 1 message.tradeCancelFlag
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.matchId
    ++ (TradeAtReferencePriceType.encode message.tradeAtReferencePriceType
    ++ (encodeUInt 1 message.subTypeOfTrade
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.tradeLegs.val.length)
    ++ (encodeUIntLE 4 message.strategyLegCount
    ++ (encodeMany TradeLegs.encode message.tradeLegs.val))))))))))))))

def decode (bytes : List UInt8) : Option (MarketDataTradeMessage × List UInt8) := do
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (matchedTime, bytes) ← decodeUIntLE 8 bytes
  let (ringSession, bytes) ← Alpha.decode 2 bytes
  let (tradeCancelFlag, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (tradeAtReferencePriceType, bytes) ← TradeAtReferencePriceType.decode bytes
  let (subTypeOfTrade, bytes) ← decodeUInt 1 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (strategyLegCount, bytes) ← decodeUIntLE 4 bytes
  let (tradeLegs_, bytes) ← decodeMany TradeLegs.decode recordCount.toNat bytes
  if fits_tradeLegs : tradeLegs_.length < 256 ^ 2 then
    pure ({ timeOfEvent, tradableInstrumentId, tradingVenue, matchedTime, ringSession, tradeCancelFlag, price, volume, matchId, tradeAtReferencePriceType, subTypeOfTrade, remainingRecords, strategyLegCount, tradeLegs := ⟨tradeLegs_, fits_tradeLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataTradeMessage) : (encode message).length ≤ 1376294 := by
  have bound_tradeLegs := message.tradeLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, TradeAtReferencePriceType.encode_length, encodeMany_length_const TradeLegs.encode 21 TradeLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeAtReferencePriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 TradeLegs.encode TradeLegs.decode TradeLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeLegs.length_lt]
  rfl

end MarketDataTradeMessage

/-- Logon Message: 12 bytes -/
structure LogonMessage where
  username : Alpha 12
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 12 bytes
  pure ({ username }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logon Response Message: 4 bytes -/
structure LogonResponseMessage where
  sessionStatus : BitVec 8
  fillerString3 : Alpha 3
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.fillerString3)

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (fillerString3, bytes) ← Alpha.decode 3 bytes
  pure ({ sessionStatus, fillerString3 }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonResponseMessage

/-- Retransmission Request Message: 12 bytes -/
structure RetransmissionRequestMessage where
  channelId : BitVec 16
  fillerString2 : Alpha 2
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (Alpha.encode message.fillerString2
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum)))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (fillerString2, bytes) ← Alpha.decode 2 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, fillerString2, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Retransmission Response Message: 12 bytes -/
structure RetransmissionResponseMessage where
  channelId : BitVec 16
  retransStatus : BitVec 8
  fillerString1 : Alpha 1
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionResponseMessage

def encode (message : RetransmissionResponseMessage) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (encodeUInt 1 message.retransStatus
    ++ (Alpha.encode message.fillerString1
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum))))

def decode (bytes : List UInt8) : Option (RetransmissionResponseMessage × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (retransStatus, bytes) ← decodeUInt 1 bytes
  let (fillerString1, bytes) ← Alpha.decode 1 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, retransStatus, fillerString1, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionResponseMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionResponseMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionResponseMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | marketStateContractMessage (message : MarketStateContractMessage) -- 311
  | marketStateInstrumentMessage (message : MarketStateInstrumentMessage) -- 312
  | indicativeOpeningPriceMessage (message : IndicativeOpeningPriceMessage) -- 320
  | quoteRequestMessage (message : QuoteRequestMessage) -- 329
  | orderBookClearMessage (message : OrderBookClearMessage) -- 327
  | crossRequestMessage (message : CrossRequestMessage) -- 330
  | topOfBookMessage (message : TopOfBookMessage) -- 321
  | marketDataTradeMessage (message : MarketDataTradeMessage) -- 341
  | logonMessage (message : LogonMessage) -- 101
  | logonResponseMessage (message : LogonResponseMessage) -- 102
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 201
  | retransmissionResponseMessage (message : RetransmissionResponseMessage) -- 202
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .marketStateContractMessage _ => 311
  | .marketStateInstrumentMessage _ => 312
  | .indicativeOpeningPriceMessage _ => 320
  | .quoteRequestMessage _ => 329
  | .orderBookClearMessage _ => 327
  | .crossRequestMessage _ => 330
  | .topOfBookMessage _ => 321
  | .marketDataTradeMessage _ => 341
  | .logonMessage _ => 101
  | .logonResponseMessage _ => 102
  | .retransmissionRequestMessage _ => 201
  | .retransmissionResponseMessage _ => 202

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .marketStateContractMessage message => MarketStateContractMessage.encode message
  | .marketStateInstrumentMessage message => MarketStateInstrumentMessage.encode message
  | .indicativeOpeningPriceMessage message => IndicativeOpeningPriceMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .crossRequestMessage message => CrossRequestMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .marketDataTradeMessage message => MarketDataTradeMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .retransmissionResponseMessage message => RetransmissionResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1376294 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | marketStateContractMessage inner =>
    simp only [encode, MarketStateContractMessage.encode_length]
    omega
  | marketStateInstrumentMessage inner =>
    simp only [encode, MarketStateInstrumentMessage.encode_length]
    omega
  | indicativeOpeningPriceMessage inner =>
    simp only [encode, IndicativeOpeningPriceMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [encode, QuoteRequestMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | crossRequestMessage inner =>
    simp only [encode, CrossRequestMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | marketDataTradeMessage inner =>
    have bound_inner := MarketDataTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [encode, RetransmissionResponseMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 311 then (MarketStateContractMessage.decode bytes).map fun (message, rest) => (.marketStateContractMessage message, rest)
  else if tag = 312 then (MarketStateInstrumentMessage.decode bytes).map fun (message, rest) => (.marketStateInstrumentMessage message, rest)
  else if tag = 320 then (IndicativeOpeningPriceMessage.decode bytes).map fun (message, rest) => (.indicativeOpeningPriceMessage message, rest)
  else if tag = 329 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 327 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 330 then (CrossRequestMessage.decode bytes).map fun (message, rest) => (.crossRequestMessage message, rest)
  else if tag = 321 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 341 then (MarketDataTradeMessage.decode bytes).map fun (message, rest) => (.marketDataTradeMessage message, rest)
  else if tag = 101 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 102 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 201 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 202 then (RetransmissionResponseMessage.decode bytes).map fun (message, rest) => (.retransmissionResponseMessage message, rest)
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
theorem encode_length_le (message : Messages) : (encode message).length ≤ 1376298 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | marketStateContractMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketStateContractMessage.encode_length]
    omega
  | marketStateInstrumentMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketStateInstrumentMessage.encode_length]
    omega
  | indicativeOpeningPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndicativeOpeningPriceMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, QuoteRequestMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderBookClearMessage.encode_length]
    omega
  | crossRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CrossRequestMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TopOfBookMessage.encode_length]
    omega
  | marketDataTradeMessage inner =>
    have bound_inner := MarketDataTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmissionResponseMessage.encode_length]
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
theorem encode_length_le (message : Packet) : (encode message).length ≤ 350956006 := by
  have bound_messages := message.messages.length_lt
  have bound_messages_items := encodeMany_length_le Messages.encode 1376298 Messages.encode_length_le message.messages.val
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

end Omi.LmeLmeselectLevel1retransmissionLmesourceV418
