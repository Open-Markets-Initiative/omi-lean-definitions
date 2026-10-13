import Wire

/-!
# The London Metal Exchange LMEsource Level3 v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectLevel3LmesourceV418

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

/-- Trade Buy Sell: one byte code -/
def TradeBuySell.codes : List UInt8 :=
  [0x42, 0x53]

inductive TradeBuySell where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeBuySell.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeBuySell

def toByte : TradeBuySell → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeBuySell :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : TradeBuySell :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeBuySell) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeBuySell) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeBuySell × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeBuySell) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeBuySell) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeBuySell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeBuySell

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

/-- Order Add Message: 68 bytes -/
structure OrderAddMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  t1 : BitVec 64
  t2 : BitVec 64
  t3 : BitVec 64
  tradableInstrumentId : BitVec 64
  orderId : BitVec 64
  buySell : BuySell
  volume : BitVec 32
  price : BitVec 64
  orderBookPosition : BitVec 32
  fillerString1 : Alpha 1
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.t1
    ++ (encodeUIntLE 8 message.t2
    ++ (encodeUIntLE 8 message.t3
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (BuySell.encode message.buySell
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderBookPosition
    ++ (Alpha.encode message.fillerString1)))))))))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (t1, bytes) ← decodeUIntLE 8 bytes
  let (t2, bytes) ← decodeUIntLE 8 bytes
  let (t3, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  let (fillerString1, bytes) ← Alpha.decode 1 bytes
  pure ({ tradingVenue, timeOfEvent, t1, t2, t3, tradableInstrumentId, orderId, buySell, volume, price, orderBookPosition, fillerString1 }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, BuySell.encode_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAddMessage

/-- Order Amend Message: 68 bytes -/
structure OrderAmendMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  t1 : BitVec 64
  t2 : BitVec 64
  t3 : BitVec 64
  tradableInstrumentId : BitVec 64
  orderId : BitVec 64
  buySell : BuySell
  volume : BitVec 32
  price : BitVec 64
  orderBookPosition : BitVec 32
  fillerString1 : Alpha 1
  deriving DecidableEq, Repr

namespace OrderAmendMessage

def encode (message : OrderAmendMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.t1
    ++ (encodeUIntLE 8 message.t2
    ++ (encodeUIntLE 8 message.t3
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (BuySell.encode message.buySell
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderBookPosition
    ++ (Alpha.encode message.fillerString1)))))))))))

def decode (bytes : List UInt8) : Option (OrderAmendMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (t1, bytes) ← decodeUIntLE 8 bytes
  let (t2, bytes) ← decodeUIntLE 8 bytes
  let (t3, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  let (fillerString1, bytes) ← Alpha.decode 1 bytes
  pure ({ tradingVenue, timeOfEvent, t1, t2, t3, tradableInstrumentId, orderId, buySell, volume, price, orderBookPosition, fillerString1 }, bytes)

@[simp] theorem encode_length (message : OrderAmendMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, BuySell.encode_length]

theorem encode_length_pos (message : OrderAmendMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAmendMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAmendMessage

/-- Order Cancel Message: 52 bytes -/
structure OrderCancelMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  t1 : BitVec 64
  t2 : BitVec 64
  t3 : BitVec 64
  tradableInstrumentId : BitVec 64
  orderId : BitVec 64
  buySell : BuySell
  fillerString1 : Alpha 1
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.t1
    ++ (encodeUIntLE 8 message.t2
    ++ (encodeUIntLE 8 message.t3
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (BuySell.encode message.buySell
    ++ (Alpha.encode message.fillerString1))))))))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (t1, bytes) ← decodeUIntLE 8 bytes
  let (t2, bytes) ← decodeUIntLE 8 bytes
  let (t3, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (fillerString1, bytes) ← Alpha.decode 1 bytes
  pure ({ tradingVenue, timeOfEvent, t1, t2, t3, tradableInstrumentId, orderId, buySell, fillerString1 }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, BuySell.encode_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelMessage

/-- Executed Legs: 29 bytes -/
structure ExecutedLegs where
  legTradableInstrumentId : BitVec 64
  legBuySell : LegBuySell
  legPrice : BitVec 64
  legVolume : BitVec 32
  legMatchId : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutedLegs

def encode (message : ExecutedLegs) : List UInt8 :=
  encodeUIntLE 8 message.legTradableInstrumentId
    ++ (LegBuySell.encode message.legBuySell
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legVolume
    ++ (encodeUIntLE 8 message.legMatchId))))

def decode (bytes : List UInt8) : Option (ExecutedLegs × List UInt8) := do
  let (legTradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (legBuySell, bytes) ← LegBuySell.decode bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legVolume, bytes) ← decodeUIntLE 4 bytes
  let (legMatchId, bytes) ← decodeUIntLE 8 bytes
  pure ({ legTradableInstrumentId, legBuySell, legPrice, legVolume, legMatchId }, bytes)

@[simp] theorem encode_length (message : ExecutedLegs) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegBuySell.encode_length]

theorem encode_length_pos (message : ExecutedLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedLegs) (rest : List UInt8) :
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

end ExecutedLegs

/-- Order Executed Message -/
structure OrderExecutedMessage where
  tradingVenue : Alpha 2
  timeOfEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  price : BitVec 64
  volume : BitVec 32
  orderId : BitVec 64
  matchId : BitVec 64
  tradeCancelFlag : BitVec 8
  subTypeOfTrade : BitVec 8
  tradeBuySell : TradeBuySell
  executedLegs : Bounded 4 ExecutedLegs
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUInt 1 message.tradeCancelFlag
    ++ (encodeUInt 1 message.subTypeOfTrade
    ++ (TradeBuySell.encode message.tradeBuySell
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.executedLegs.val.length)
    ++ (encodeMany ExecutedLegs.encode message.executedLegs.val)))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (tradeCancelFlag, bytes) ← decodeUInt 1 bytes
  let (subTypeOfTrade, bytes) ← decodeUInt 1 bytes
  let (tradeBuySell, bytes) ← TradeBuySell.decode bytes
  let (strategyLegCount, bytes) ← decodeUIntLE 4 bytes
  let (executedLegs_, bytes) ← decodeMany ExecutedLegs.decode strategyLegCount.toNat bytes
  if fits_executedLegs : executedLegs_.length < 256 ^ 4 then
    pure ({ tradingVenue, timeOfEvent, tradableInstrumentId, price, volume, orderId, matchId, tradeCancelFlag, subTypeOfTrade, tradeBuySell, executedLegs := ⟨executedLegs_, fits_executedLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecutedMessage) : (encode message).length ≤ 124554051608 := by
  have bound_executedLegs := message.executedLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, TradeBuySell.encode_length, encodeMany_length_const ExecutedLegs.encode 29 ExecutedLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeBuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 ExecutedLegs.encode ExecutedLegs.decode ExecutedLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.executedLegs.length_lt]
  rfl

end OrderExecutedMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | marketStateContractMessage (message : MarketStateContractMessage) -- 311
  | marketStateInstrumentMessage (message : MarketStateInstrumentMessage) -- 312
  | indicativeOpeningPriceMessage (message : IndicativeOpeningPriceMessage) -- 320
  | quoteRequestMessage (message : QuoteRequestMessage) -- 329
  | orderBookClearMessage (message : OrderBookClearMessage) -- 327
  | crossRequestMessage (message : CrossRequestMessage) -- 330
  | orderAddMessage (message : OrderAddMessage) -- 323
  | orderAmendMessage (message : OrderAmendMessage) -- 324
  | orderCancelMessage (message : OrderCancelMessage) -- 325
  | orderExecutedMessage (message : OrderExecutedMessage) -- 326
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
  | .orderAddMessage _ => 323
  | .orderAmendMessage _ => 324
  | .orderCancelMessage _ => 325
  | .orderExecutedMessage _ => 326

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .marketStateContractMessage message => MarketStateContractMessage.encode message
  | .marketStateInstrumentMessage message => MarketStateInstrumentMessage.encode message
  | .indicativeOpeningPriceMessage message => IndicativeOpeningPriceMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .crossRequestMessage message => CrossRequestMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderAmendMessage message => OrderAmendMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 124554051608 := by
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
  | orderAddMessage inner =>
    simp only [encode, OrderAddMessage.encode_length]
    omega
  | orderAmendMessage inner =>
    simp only [encode, OrderAmendMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    have bound_inner := OrderExecutedMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 311 then (MarketStateContractMessage.decode bytes).map fun (message, rest) => (.marketStateContractMessage message, rest)
  else if tag = 312 then (MarketStateInstrumentMessage.decode bytes).map fun (message, rest) => (.marketStateInstrumentMessage message, rest)
  else if tag = 320 then (IndicativeOpeningPriceMessage.decode bytes).map fun (message, rest) => (.indicativeOpeningPriceMessage message, rest)
  else if tag = 329 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 327 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 330 then (CrossRequestMessage.decode bytes).map fun (message, rest) => (.crossRequestMessage message, rest)
  else if tag = 323 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 324 then (OrderAmendMessage.decode bytes).map fun (message, rest) => (.orderAmendMessage message, rest)
  else if tag = 325 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 326 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
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
theorem encode_length_le (message : Messages) : (encode message).length ≤ 124554051612 := by
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
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAddMessage.encode_length]
    omega
  | orderAmendMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAmendMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancelMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    have bound_inner := OrderExecutedMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
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
theorem encode_length_le (message : Packet) : (encode message).length ≤ 31761283161076 := by
  have bound_messages := message.messages.length_lt
  have bound_messages_items := encodeMany_length_le Messages.encode 124554051612 Messages.encode_length_le message.messages.val
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

end Omi.LmeLmeselectLevel3LmesourceV418
