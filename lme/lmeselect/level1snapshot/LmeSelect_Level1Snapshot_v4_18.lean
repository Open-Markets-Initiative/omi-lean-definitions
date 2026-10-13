import Wire

/-!
# The London Metal Exchange LMEsource Level1 Refresh v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectLevel1snapshotLmesourceV418

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

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | marketStateContractMessage (message : MarketStateContractMessage) -- 311
  | marketStateInstrumentMessage (message : MarketStateInstrumentMessage) -- 312
  | indicativeOpeningPriceMessage (message : IndicativeOpeningPriceMessage) -- 320
  | quoteRequestMessage (message : QuoteRequestMessage) -- 329
  | topOfBookMessage (message : TopOfBookMessage) -- 321
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .marketStateContractMessage _ => 311
  | .marketStateInstrumentMessage _ => 312
  | .indicativeOpeningPriceMessage _ => 320
  | .quoteRequestMessage _ => 329
  | .topOfBookMessage _ => 321
  | .refreshCompleteMessage _ => 203

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .marketStateContractMessage message => MarketStateContractMessage.encode message
  | .marketStateInstrumentMessage message => MarketStateInstrumentMessage.encode message
  | .indicativeOpeningPriceMessage message => IndicativeOpeningPriceMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 98 := by
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
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 311 then (MarketStateContractMessage.decode bytes).map fun (message, rest) => (.marketStateContractMessage message, rest)
  else if tag = 312 then (MarketStateInstrumentMessage.decode bytes).map fun (message, rest) => (.marketStateInstrumentMessage message, rest)
  else if tag = 320 then (IndicativeOpeningPriceMessage.decode bytes).map fun (message, rest) => (.indicativeOpeningPriceMessage message, rest)
  else if tag = 329 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 321 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 102 := by
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
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TopOfBookMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
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
theorem encode_length_le (message : Packet) : (encode message).length ≤ 26026 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 102 Message.encode_length_le message.message.val
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

end Omi.LmeLmeselectLevel1snapshotLmesourceV418
