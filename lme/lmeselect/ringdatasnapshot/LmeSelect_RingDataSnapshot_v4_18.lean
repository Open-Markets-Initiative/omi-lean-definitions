import Wire

/-!
# The London Metal Exchange LMEsource RingData Refresh v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectRingdatasnapshotLmesourceV418

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

/-- Market State Product Message: 15 bytes -/
structure MarketStateProductMessage where
  tradingVenue : Alpha 2
  timeofEvent : BitVec 64
  productCode : Alpha 2
  tradingState : BitVec 8
  ringSession : Alpha 2
  deriving DecidableEq, Repr

namespace MarketStateProductMessage

def encode (message : MarketStateProductMessage) : List UInt8 :=
  Alpha.encode message.tradingVenue
    ++ (encodeUIntLE 8 message.timeofEvent
    ++ (Alpha.encode message.productCode
    ++ (encodeUInt 1 message.tradingState
    ++ (Alpha.encode message.ringSession))))

def decode (bytes : List UInt8) : Option (MarketStateProductMessage × List UInt8) := do
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (timeofEvent, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (tradingState, bytes) ← decodeUInt 1 bytes
  let (ringSession, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingVenue, timeofEvent, productCode, tradingState, ringSession }, bytes)

@[simp] theorem encode_length (message : MarketStateProductMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MarketStateProductMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateProductMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketStateProductMessage

/-- Order Legs: 13 bytes -/
structure OrderLegs where
  legBuySell : LegBuySell
  legPrice : BitVec 64
  legVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OrderLegs

def encode (message : OrderLegs) : List UInt8 :=
  LegBuySell.encode message.legBuySell
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legVolume))

def decode (bytes : List UInt8) : Option (OrderLegs × List UInt8) := do
  let (legBuySell, bytes) ← LegBuySell.decode bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ legBuySell, legPrice, legVolume }, bytes)

@[simp] theorem encode_length (message : OrderLegs) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LegBuySell.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegBuySell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderLegs

/-- Market Data Order Message -/
structure MarketDataOrderMessage where
  timeofEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  tradingVenue : Alpha 2
  ringSession : Alpha 2
  cancellationReason : Alpha 2
  productCode : Alpha 2
  buySell : BuySell
  price : BitVec 64
  volume : BitVec 32
  remainingRecords : BitVec 16
  strategyLegCount : BitVec 32
  orderLegs : Bounded 2 OrderLegs
  deriving DecidableEq, Repr

namespace MarketDataOrderMessage

def encode (message : MarketDataOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeofEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (Alpha.encode message.tradingVenue
    ++ (Alpha.encode message.ringSession
    ++ (Alpha.encode message.cancellationReason
    ++ (Alpha.encode message.productCode
    ++ (BuySell.encode message.buySell
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.orderLegs.val.length)
    ++ (encodeUIntLE 4 message.strategyLegCount
    ++ (encodeMany OrderLegs.encode message.orderLegs.val))))))))))))

def decode (bytes : List UInt8) : Option (MarketDataOrderMessage × List UInt8) := do
  let (timeofEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (ringSession, bytes) ← Alpha.decode 2 bytes
  let (cancellationReason, bytes) ← Alpha.decode 2 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (buySell, bytes) ← BuySell.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (strategyLegCount, bytes) ← decodeUIntLE 4 bytes
  let (orderLegs_, bytes) ← decodeMany OrderLegs.decode recordCount.toNat bytes
  if fits_orderLegs : orderLegs_.length < 256 ^ 2 then
    pure ({ timeofEvent, tradableInstrumentId, tradingVenue, ringSession, cancellationReason, productCode, buySell, price, volume, remainingRecords, strategyLegCount, orderLegs := ⟨orderLegs_, fits_orderLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataOrderMessage) : (encode message).length ≤ 852000 := by
  have bound_orderLegs := message.orderLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, BuySell.encode_length, encodeMany_length_const OrderLegs.encode 13 OrderLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySell.decode_encode, some_bind]
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
  rw [decodeMany_bounded 2 OrderLegs.encode OrderLegs.decode OrderLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderLegs.length_lt]
  rfl

end MarketDataOrderMessage

/-- Indicative Trade Price Message: 29 bytes -/
structure IndicativeTradePriceMessage where
  timeofEvent : BitVec 64
  tradableInstrumentId : BitVec 64
  tradingVenue : Alpha 2
  ringSession : Alpha 2
  indicativePriceType : BitVec 8
  indicativeTradePrice : BitVec 64
  deriving DecidableEq, Repr

namespace IndicativeTradePriceMessage

def encode (message : IndicativeTradePriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeofEvent
    ++ (encodeUIntLE 8 message.tradableInstrumentId
    ++ (Alpha.encode message.tradingVenue
    ++ (Alpha.encode message.ringSession
    ++ (encodeUInt 1 message.indicativePriceType
    ++ (encodeUIntLE 8 message.indicativeTradePrice)))))

def decode (bytes : List UInt8) : Option (IndicativeTradePriceMessage × List UInt8) := do
  let (timeofEvent, bytes) ← decodeUIntLE 8 bytes
  let (tradableInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingVenue, bytes) ← Alpha.decode 2 bytes
  let (ringSession, bytes) ← Alpha.decode 2 bytes
  let (indicativePriceType, bytes) ← decodeUInt 1 bytes
  let (indicativeTradePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ timeofEvent, tradableInstrumentId, tradingVenue, ringSession, indicativePriceType, indicativeTradePrice }, bytes)

@[simp] theorem encode_length (message : IndicativeTradePriceMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IndicativeTradePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativeTradePriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicativeTradePriceMessage

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
  timeofEvent : BitVec 64
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
  encodeUIntLE 8 message.timeofEvent
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
  let (timeofEvent, bytes) ← decodeUIntLE 8 bytes
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
    pure ({ timeofEvent, tradableInstrumentId, tradingVenue, matchedTime, ringSession, tradeCancelFlag, price, volume, matchId, tradeAtReferencePriceType, subTypeOfTrade, remainingRecords, strategyLegCount, tradeLegs := ⟨tradeLegs_, fits_tradeLegs⟩ }, bytes)
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
  | marketStateProductMessage (message : MarketStateProductMessage) -- 310
  | marketDataOrderMessage (message : MarketDataOrderMessage) -- 328
  | indicativeTradePriceMessage (message : IndicativeTradePriceMessage) -- 340
  | marketDataTradeMessage (message : MarketDataTradeMessage) -- 341
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .marketStateProductMessage _ => 310
  | .marketDataOrderMessage _ => 328
  | .indicativeTradePriceMessage _ => 340
  | .marketDataTradeMessage _ => 341
  | .refreshCompleteMessage _ => 203

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .marketStateProductMessage message => MarketStateProductMessage.encode message
  | .marketDataOrderMessage message => MarketDataOrderMessage.encode message
  | .indicativeTradePriceMessage message => IndicativeTradePriceMessage.encode message
  | .marketDataTradeMessage message => MarketDataTradeMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1376294 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | marketStateProductMessage inner =>
    simp only [encode, MarketStateProductMessage.encode_length]
    omega
  | marketDataOrderMessage inner =>
    have bound_inner := MarketDataOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | indicativeTradePriceMessage inner =>
    simp only [encode, IndicativeTradePriceMessage.encode_length]
    omega
  | marketDataTradeMessage inner =>
    have bound_inner := MarketDataTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 310 then (MarketStateProductMessage.decode bytes).map fun (message, rest) => (.marketStateProductMessage message, rest)
  else if tag = 328 then (MarketDataOrderMessage.decode bytes).map fun (message, rest) => (.marketDataOrderMessage message, rest)
  else if tag = 340 then (IndicativeTradePriceMessage.decode bytes).map fun (message, rest) => (.indicativeTradePriceMessage message, rest)
  else if tag = 341 then (MarketDataTradeMessage.decode bytes).map fun (message, rest) => (.marketDataTradeMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
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
  | marketStateProductMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketStateProductMessage.encode_length]
    omega
  | marketDataOrderMessage inner =>
    have bound_inner := MarketDataOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | indicativeTradePriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndicativeTradePriceMessage.encode_length]
    omega
  | marketDataTradeMessage inner =>
    have bound_inner := MarketDataTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
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

end Omi.LmeLmeselectRingdatasnapshotLmesourceV418
