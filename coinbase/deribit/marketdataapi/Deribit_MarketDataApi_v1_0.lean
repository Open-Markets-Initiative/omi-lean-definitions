import Omi.Wire

/-!
# Coinbase Market Data Api v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Type is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: a Message Count of 0 marks Empty Packet and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Message Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Taker Flags is a bit field set, proven as its 4 byte integer rather than bit by bit.

Note: Maker Flags is a bit field set, proven as its 4 byte integer rather than bit by bit.

Note: Md Message's body has no bound its 2 byte Message Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseDeribitMarketdataapiSbeV10

/-- Instrument Definition Message large Tick Sizes Group: 16 bytes -/
structure InstrumentDefinitionMessageLargeTickSizesGroup where
  largeTickSize : BitVec 64
  thresholdPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessageLargeTickSizesGroup

def encode (message : InstrumentDefinitionMessageLargeTickSizesGroup) : List UInt8 :=
  encodeUIntLE 8 message.largeTickSize
    ++ (encodeUIntLE 8 message.thresholdPrice)

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessageLargeTickSizesGroup × List UInt8) := do
  let (largeTickSize, bytes) ← decodeUIntLE 8 bytes
  let (thresholdPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ largeTickSize, thresholdPrice }, bytes)

@[simp] theorem encode_length (message : InstrumentDefinitionMessageLargeTickSizesGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentDefinitionMessageLargeTickSizesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDefinitionMessageLargeTickSizesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentDefinitionMessageLargeTickSizesGroup

/-- Instrument Definition Message large Tick Sizes Groups -/
structure InstrumentDefinitionMessageLargeTickSizesGroups where
  blockLength : BitVec 16
  instrumentDefinitionMessageLargeTickSizesGroup : Bounded 2 InstrumentDefinitionMessageLargeTickSizesGroup
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessageLargeTickSizesGroups

def encode (message : InstrumentDefinitionMessageLargeTickSizesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrumentDefinitionMessageLargeTickSizesGroup.val.length)
    ++ (encodeMany InstrumentDefinitionMessageLargeTickSizesGroup.encode message.instrumentDefinitionMessageLargeTickSizesGroup.val))

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessageLargeTickSizesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (instrumentDefinitionMessageLargeTickSizesGroup_, bytes) ← decodeMany InstrumentDefinitionMessageLargeTickSizesGroup.decode numInGroup.toNat bytes
  if fits_instrumentDefinitionMessageLargeTickSizesGroup : instrumentDefinitionMessageLargeTickSizesGroup_.length < 256 ^ 2 then
    pure ({ blockLength, instrumentDefinitionMessageLargeTickSizesGroup := ⟨instrumentDefinitionMessageLargeTickSizesGroup_, fits_instrumentDefinitionMessageLargeTickSizesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrumentDefinitionMessageLargeTickSizesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentDefinitionMessageLargeTickSizesGroups) : (encode message).length ≤ 1048564 := by
  have bound_instrumentDefinitionMessageLargeTickSizesGroup := message.instrumentDefinitionMessageLargeTickSizesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const InstrumentDefinitionMessageLargeTickSizesGroup.encode 16 InstrumentDefinitionMessageLargeTickSizesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrumentDefinitionMessageLargeTickSizesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrumentDefinitionMessageLargeTickSizesGroup.encode InstrumentDefinitionMessageLargeTickSizesGroup.decode InstrumentDefinitionMessageLargeTickSizesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentDefinitionMessageLargeTickSizesGroup.length_lt]
  rfl

end InstrumentDefinitionMessageLargeTickSizesGroups

/-- Instrument Definition Message legs Group: 9 bytes -/
structure InstrumentDefinitionMessageLegsGroup where
  legInstrumentId : BitVec 64
  ratio : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessageLegsGroup

def encode (message : InstrumentDefinitionMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legInstrumentId
    ++ (encodeUInt 1 message.ratio)

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessageLegsGroup × List UInt8) := do
  let (legInstrumentId, bytes) ← decodeUIntLE 8 bytes
  let (ratio, bytes) ← decodeUInt 1 bytes
  pure ({ legInstrumentId, ratio }, bytes)

@[simp] theorem encode_length (message : InstrumentDefinitionMessageLegsGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : InstrumentDefinitionMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDefinitionMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentDefinitionMessageLegsGroup

/-- Instrument Definition Message legs Groups -/
structure InstrumentDefinitionMessageLegsGroups where
  blockLength : BitVec 16
  instrumentDefinitionMessageLegsGroup : Bounded 2 InstrumentDefinitionMessageLegsGroup
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessageLegsGroups

def encode (message : InstrumentDefinitionMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrumentDefinitionMessageLegsGroup.val.length)
    ++ (encodeMany InstrumentDefinitionMessageLegsGroup.encode message.instrumentDefinitionMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (instrumentDefinitionMessageLegsGroup_, bytes) ← decodeMany InstrumentDefinitionMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_instrumentDefinitionMessageLegsGroup : instrumentDefinitionMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, instrumentDefinitionMessageLegsGroup := ⟨instrumentDefinitionMessageLegsGroup_, fits_instrumentDefinitionMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrumentDefinitionMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentDefinitionMessageLegsGroups) : (encode message).length ≤ 589819 := by
  have bound_instrumentDefinitionMessageLegsGroup := message.instrumentDefinitionMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const InstrumentDefinitionMessageLegsGroup.encode 9 InstrumentDefinitionMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrumentDefinitionMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrumentDefinitionMessageLegsGroup.encode InstrumentDefinitionMessageLegsGroup.decode InstrumentDefinitionMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentDefinitionMessageLegsGroup.length_lt]
  rfl

end InstrumentDefinitionMessageLegsGroups

/-- Instrument Definition Message -/
structure InstrumentDefinitionMessage where
  instrumentId : BitVec 64
  name : Alpha 128
  indexId : BitVec 64
  underlying : Alpha 64
  quantityAsset : Alpha 8
  priceAsset : Alpha 8
  expiryTime : BitVec 64
  strikePrice : BitVec 64
  minOrderQuantity : BitVec 64
  tickSize : BitVec 64
  quantityExponent : BitVec 8
  type : BitVec 8
  flags : BitVec 8
  status : BitVec 8
  instrumentDefinitionMessageLargeTickSizesGroups : InstrumentDefinitionMessageLargeTickSizesGroups
  instrumentDefinitionMessageLegsGroups : InstrumentDefinitionMessageLegsGroups
  deriving DecidableEq, Repr

namespace InstrumentDefinitionMessage

def encode (message : InstrumentDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.name
    ++ (encodeUIntLE 8 message.indexId
    ++ (Alpha.encode message.underlying
    ++ (Alpha.encode message.quantityAsset
    ++ (Alpha.encode message.priceAsset
    ++ (encodeUIntLE 8 message.expiryTime
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.minOrderQuantity
    ++ (encodeUIntLE 8 message.tickSize
    ++ (encodeUInt 1 message.quantityExponent
    ++ (encodeUInt 1 message.type
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUInt 1 message.status
    ++ (InstrumentDefinitionMessageLargeTickSizesGroups.encode message.instrumentDefinitionMessageLargeTickSizesGroups
    ++ (InstrumentDefinitionMessageLegsGroups.encode message.instrumentDefinitionMessageLegsGroups)))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDefinitionMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (name, bytes) ← Alpha.decode 128 bytes
  let (indexId, bytes) ← decodeUIntLE 8 bytes
  let (underlying, bytes) ← Alpha.decode 64 bytes
  let (quantityAsset, bytes) ← Alpha.decode 8 bytes
  let (priceAsset, bytes) ← Alpha.decode 8 bytes
  let (expiryTime, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (minOrderQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (quantityExponent, bytes) ← decodeUInt 1 bytes
  let (type, bytes) ← decodeUInt 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (instrumentDefinitionMessageLargeTickSizesGroups, bytes) ← InstrumentDefinitionMessageLargeTickSizesGroups.decode bytes
  let (instrumentDefinitionMessageLegsGroups, bytes) ← InstrumentDefinitionMessageLegsGroups.decode bytes
  pure ({ instrumentId, name, indexId, underlying, quantityAsset, priceAsset, expiryTime, strikePrice, minOrderQuantity, tickSize, quantityExponent, type, flags, status, instrumentDefinitionMessageLargeTickSizesGroups, instrumentDefinitionMessageLegsGroups }, bytes)

theorem encode_length_pos (message : InstrumentDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentDefinitionMessage) : (encode message).length ≤ 1638643 := by
  have bound_instrumentDefinitionMessageLargeTickSizesGroups := InstrumentDefinitionMessageLargeTickSizesGroups.encode_length_le message.instrumentDefinitionMessageLargeTickSizesGroups
  have bound_instrumentDefinitionMessageLegsGroups := InstrumentDefinitionMessageLegsGroups.encode_length_le message.instrumentDefinitionMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : InstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentDefinitionMessageLargeTickSizesGroups.decode_encode, some_bind]
  dsimp only
  rw [InstrumentDefinitionMessageLegsGroups.decode_encode, some_bind]
  rfl

end InstrumentDefinitionMessage

/-- Index Definition Message: 136 bytes -/
structure IndexDefinitionMessage where
  indexId : BitVec 64
  name : Alpha 128
  deriving DecidableEq, Repr

namespace IndexDefinitionMessage

def encode (message : IndexDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.indexId
    ++ (Alpha.encode message.name)

def decode (bytes : List UInt8) : Option (IndexDefinitionMessage × List UInt8) := do
  let (indexId, bytes) ← decodeUIntLE 8 bytes
  let (name, bytes) ← Alpha.decode 128 bytes
  pure ({ indexId, name }, bytes)

@[simp] theorem encode_length (message : IndexDefinitionMessage) : (encode message).length = 136 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexDefinitionMessage

/-- Instrument Info Message: 40 bytes -/
structure InstrumentInfoMessage where
  instrumentId : BitVec 64
  minSellPrice : BitVec 64
  maxBuyPrice : BitVec 64
  indexPrice : BitVec 64
  markPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentInfoMessage

def encode (message : InstrumentInfoMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.minSellPrice
    ++ (encodeUIntLE 8 message.maxBuyPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (encodeUIntLE 8 message.markPrice))))

def decode (bytes : List UInt8) : Option (InstrumentInfoMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (minSellPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxBuyPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, minSellPrice, maxBuyPrice, indexPrice, markPrice }, bytes)

@[simp] theorem encode_length (message : InstrumentInfoMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentInfoMessage) (rest : List UInt8) :
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

end InstrumentInfoMessage

/-- Instrument Ref Message: 48 bytes -/
structure InstrumentRefMessage where
  instrumentId : BitVec 64
  currentFunding : Alpha 8
  funding8h : Alpha 8
  estimatedDeliveryPrice : BitVec 64
  deliveryPrice : BitVec 64
  settlementPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentRefMessage

def encode (message : InstrumentRefMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.currentFunding
    ++ (Alpha.encode message.funding8h
    ++ (encodeUIntLE 8 message.estimatedDeliveryPrice
    ++ (encodeUIntLE 8 message.deliveryPrice
    ++ (encodeUIntLE 8 message.settlementPrice)))))

def decode (bytes : List UInt8) : Option (InstrumentRefMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (currentFunding, bytes) ← Alpha.decode 8 bytes
  let (funding8h, bytes) ← Alpha.decode 8 bytes
  let (estimatedDeliveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (deliveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, currentFunding, funding8h, estimatedDeliveryPrice, deliveryPrice, settlementPrice }, bytes)

@[simp] theorem encode_length (message : InstrumentRefMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentRefMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentRefMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentRefMessage

/-- Instrument Status Update Message: 9 bytes -/
structure InstrumentStatusUpdateMessage where
  instrumentId : BitVec 64
  tradingStatus : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentStatusUpdateMessage

def encode (message : InstrumentStatusUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUInt 1 message.tradingStatus)

def decode (bytes : List UInt8) : Option (InstrumentStatusUpdateMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  pure ({ instrumentId, tradingStatus }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusUpdateMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : InstrumentStatusUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentStatusUpdateMessage

/-- Bid Put Message: 40 bytes -/
structure BidPutMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  price : BitVec 64
  sortOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace BidPutMessage

def encode (message : BidPutMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.sortOrderId))))

def decode (bytes : List UInt8) : Option (BidPutMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (sortOrderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa, price, sortOrderId }, bytes)

@[simp] theorem encode_length (message : BidPutMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidPutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPutMessage) (rest : List UInt8) :
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

end BidPutMessage

/-- Ask Put Message: 40 bytes -/
structure AskPutMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  price : BitVec 64
  sortOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace AskPutMessage

def encode (message : AskPutMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.sortOrderId))))

def decode (bytes : List UInt8) : Option (AskPutMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (sortOrderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa, price, sortOrderId }, bytes)

@[simp] theorem encode_length (message : AskPutMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskPutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPutMessage) (rest : List UInt8) :
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

end AskPutMessage

/-- Bid Qty Reduced Message: 24 bytes -/
structure BidQtyReducedMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  deriving DecidableEq, Repr

namespace BidQtyReducedMessage

def encode (message : BidQtyReducedMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa))

def decode (bytes : List UInt8) : Option (BidQtyReducedMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa }, bytes)

@[simp] theorem encode_length (message : BidQtyReducedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidQtyReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidQtyReducedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BidQtyReducedMessage

/-- Ask Qty Reduced Message: 24 bytes -/
structure AskQtyReducedMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  deriving DecidableEq, Repr

namespace AskQtyReducedMessage

def encode (message : AskQtyReducedMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa))

def decode (bytes : List UInt8) : Option (AskQtyReducedMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa }, bytes)

@[simp] theorem encode_length (message : AskQtyReducedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskQtyReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskQtyReducedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AskQtyReducedMessage

/-- Bid Delete Message: 16 bytes -/
structure BidDeleteMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace BidDeleteMessage

def encode (message : BidDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId)

def decode (bytes : List UInt8) : Option (BidDeleteMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId }, bytes)

@[simp] theorem encode_length (message : BidDeleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BidDeleteMessage

/-- Ask Delete Message: 16 bytes -/
structure AskDeleteMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace AskDeleteMessage

def encode (message : AskDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId)

def decode (bytes : List UInt8) : Option (AskDeleteMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId }, bytes)

@[simp] theorem encode_length (message : AskDeleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AskDeleteMessage

/-- Trade Summary Message: 56 bytes -/
structure TradeSummaryMessage where
  instrumentId : BitVec 64
  takerOrderId : BitVec 64
  totalFilledMantissa : BitVec 64
  deepestPrice : BitVec 64
  markPrice : BitVec 64
  indexPrice : BitVec 64
  tradeCount : BitVec 32
  takerFlags : BitVec 32
  deriving DecidableEq, Repr

namespace TradeSummaryMessage

def encode (message : TradeSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.takerOrderId
    ++ (encodeUIntLE 8 message.totalFilledMantissa
    ++ (encodeUIntLE 8 message.deepestPrice
    ++ (encodeUIntLE 8 message.markPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (encodeUIntLE 4 message.tradeCount
    ++ (encodeUIntLE 4 message.takerFlags)))))))

def decode (bytes : List UInt8) : Option (TradeSummaryMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (takerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (totalFilledMantissa, bytes) ← decodeUIntLE 8 bytes
  let (deepestPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeCount, bytes) ← decodeUIntLE 4 bytes
  let (takerFlags, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, takerOrderId, totalFilledMantissa, deepestPrice, markPrice, indexPrice, tradeCount, takerFlags }, bytes)

@[simp] theorem encode_length (message : TradeSummaryMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSummaryMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeSummaryMessage

/-- Trade Message: 44 bytes -/
structure TradeMessage where
  matchId : BitVec 64
  instrumentId : BitVec 64
  makerOrderId : BitVec 64
  fillQtyMantissa : BitVec 64
  fillPrice : BitVec 64
  makerFlags : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.makerOrderId
    ++ (encodeUIntLE 8 message.fillQtyMantissa
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 4 message.makerFlags)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (makerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (fillQtyMantissa, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (makerFlags, bytes) ← decodeUIntLE 4 bytes
  pure ({ matchId, instrumentId, makerOrderId, fillQtyMantissa, fillPrice, makerFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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

end TradeMessage

/-- Block Trade Message: 78 bytes -/
structure BlockTradeMessage where
  matchId : BitVec 64
  instrumentId : BitVec 64
  blockTradeId : BitVec 64
  blockRfqId : BitVec 64
  fillQtyMantissa : BitVec 64
  fillPrice : BitVec 64
  markPrice : BitVec 64
  indexPrice : BitVec 64
  impliedVolatility : Alpha 8
  takerFlags : BitVec 32
  numberOfLegs : BitVec 16
  deriving DecidableEq, Repr

namespace BlockTradeMessage

def encode (message : BlockTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.blockTradeId
    ++ (encodeUIntLE 8 message.blockRfqId
    ++ (encodeUIntLE 8 message.fillQtyMantissa
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 8 message.markPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (Alpha.encode message.impliedVolatility
    ++ (encodeUIntLE 4 message.takerFlags
    ++ (encodeUIntLE 2 message.numberOfLegs))))))))))

def decode (bytes : List UInt8) : Option (BlockTradeMessage × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (blockTradeId, bytes) ← decodeUIntLE 8 bytes
  let (blockRfqId, bytes) ← decodeUIntLE 8 bytes
  let (fillQtyMantissa, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (impliedVolatility, bytes) ← Alpha.decode 8 bytes
  let (takerFlags, bytes) ← decodeUIntLE 4 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 2 bytes
  pure ({ matchId, instrumentId, blockTradeId, blockRfqId, fillQtyMantissa, fillPrice, markPrice, indexPrice, impliedVolatility, takerFlags, numberOfLegs }, bytes)

@[simp] theorem encode_length (message : BlockTradeMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BlockTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BlockTradeMessage

/-- Snapshot Header Message: 24 bytes -/
structure SnapshotHeaderMessage where
  instrumentId : BitVec 64
  incrementalTimestamp : BitVec 64
  incrementalSeqNum : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotHeaderMessage

def encode (message : SnapshotHeaderMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.incrementalTimestamp
    ++ (encodeUIntLE 8 message.incrementalSeqNum))

def decode (bytes : List UInt8) : Option (SnapshotHeaderMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (incrementalTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (incrementalSeqNum, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, incrementalTimestamp, incrementalSeqNum }, bytes)

@[simp] theorem encode_length (message : SnapshotHeaderMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotHeaderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotHeaderMessage

/-- Snapshot Trailer Message: 24 bytes -/
structure SnapshotTrailerMessage where
  instrumentId : BitVec 64
  timestamp : BitVec 64
  incrementSeqNum : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotTrailerMessage

def encode (message : SnapshotTrailerMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.incrementSeqNum))

def decode (bytes : List UInt8) : Option (SnapshotTrailerMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (incrementSeqNum, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, timestamp, incrementSeqNum }, bytes)

@[simp] theorem encode_length (message : SnapshotTrailerMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotTrailerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotTrailerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotTrailerMessage

/-- End Of Cycle Message: 4 bytes -/
structure EndOfCycleMessage where
  activeInstrumentCount : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfCycleMessage

def encode (message : EndOfCycleMessage) : List UInt8 :=
  encodeUIntLE 4 message.activeInstrumentCount

def decode (bytes : List UInt8) : Option (EndOfCycleMessage × List UInt8) := do
  let (activeInstrumentCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ activeInstrumentCount }, bytes)

@[simp] theorem encode_length (message : EndOfCycleMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : EndOfCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EndOfCycleMessage

/-- Retransmit Request Message: 9 bytes -/
structure RetransmitRequestMessage where
  beginSeqNum : BitVec 64
  messageCountShort : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRequestMessage

def encode (message : RetransmitRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.beginSeqNum
    ++ (encodeUInt 1 message.messageCountShort)

def decode (bytes : List UInt8) : Option (RetransmitRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (messageCountShort, bytes) ← decodeUInt 1 bytes
  pure ({ beginSeqNum, messageCountShort }, bytes)

@[simp] theorem encode_length (message : RetransmitRequestMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmitRequestMessage

/-- Retransmit Reject Message: 49 bytes -/
structure RetransmitRejectMessage where
  retryDelayNanos : BitVec 64
  details : Alpha 40
  reason : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRejectMessage

def encode (message : RetransmitRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.retryDelayNanos
    ++ (Alpha.encode message.details
    ++ (encodeUInt 1 message.reason))

def decode (bytes : List UInt8) : Option (RetransmitRejectMessage × List UInt8) := do
  let (retryDelayNanos, bytes) ← decodeUIntLE 8 bytes
  let (details, bytes) ← Alpha.decode 40 bytes
  let (reason, bytes) ← decodeUInt 1 bytes
  pure ({ retryDelayNanos, details, reason }, bytes)

@[simp] theorem encode_length (message : RetransmitRejectMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmitRejectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentDefinitionMessage (message : InstrumentDefinitionMessage) -- 10
  | indexDefinitionMessage (message : IndexDefinitionMessage) -- 11
  | instrumentInfoMessage (message : InstrumentInfoMessage) -- 14
  | instrumentRefMessage (message : InstrumentRefMessage) -- 15
  | instrumentStatusUpdateMessage (message : InstrumentStatusUpdateMessage) -- 16
  | bidPutMessage (message : BidPutMessage) -- 20
  | askPutMessage (message : AskPutMessage) -- 21
  | bidQtyReducedMessage (message : BidQtyReducedMessage) -- 22
  | askQtyReducedMessage (message : AskQtyReducedMessage) -- 23
  | bidDeleteMessage (message : BidDeleteMessage) -- 24
  | askDeleteMessage (message : AskDeleteMessage) -- 25
  | tradeSummaryMessage (message : TradeSummaryMessage) -- 30
  | tradeMessage (message : TradeMessage) -- 31
  | blockTradeMessage (message : BlockTradeMessage) -- 33
  | snapshotHeaderMessage (message : SnapshotHeaderMessage) -- 100
  | snapshotTrailerMessage (message : SnapshotTrailerMessage) -- 101
  | endOfCycleMessage (message : EndOfCycleMessage) -- 119
  | retransmitRequestMessage (message : RetransmitRequestMessage) -- 200
  | retransmitRejectMessage (message : RetransmitRejectMessage) -- 202
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .instrumentDefinitionMessage _ => 10
  | .indexDefinitionMessage _ => 11
  | .instrumentInfoMessage _ => 14
  | .instrumentRefMessage _ => 15
  | .instrumentStatusUpdateMessage _ => 16
  | .bidPutMessage _ => 20
  | .askPutMessage _ => 21
  | .bidQtyReducedMessage _ => 22
  | .askQtyReducedMessage _ => 23
  | .bidDeleteMessage _ => 24
  | .askDeleteMessage _ => 25
  | .tradeSummaryMessage _ => 30
  | .tradeMessage _ => 31
  | .blockTradeMessage _ => 33
  | .snapshotHeaderMessage _ => 100
  | .snapshotTrailerMessage _ => 101
  | .endOfCycleMessage _ => 119
  | .retransmitRequestMessage _ => 200
  | .retransmitRejectMessage _ => 202

def encode : Payload → List UInt8
  | .instrumentDefinitionMessage message => InstrumentDefinitionMessage.encode message
  | .indexDefinitionMessage message => IndexDefinitionMessage.encode message
  | .instrumentInfoMessage message => InstrumentInfoMessage.encode message
  | .instrumentRefMessage message => InstrumentRefMessage.encode message
  | .instrumentStatusUpdateMessage message => InstrumentStatusUpdateMessage.encode message
  | .bidPutMessage message => BidPutMessage.encode message
  | .askPutMessage message => AskPutMessage.encode message
  | .bidQtyReducedMessage message => BidQtyReducedMessage.encode message
  | .askQtyReducedMessage message => AskQtyReducedMessage.encode message
  | .bidDeleteMessage message => BidDeleteMessage.encode message
  | .askDeleteMessage message => AskDeleteMessage.encode message
  | .tradeSummaryMessage message => TradeSummaryMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .blockTradeMessage message => BlockTradeMessage.encode message
  | .snapshotHeaderMessage message => SnapshotHeaderMessage.encode message
  | .snapshotTrailerMessage message => SnapshotTrailerMessage.encode message
  | .endOfCycleMessage message => EndOfCycleMessage.encode message
  | .retransmitRequestMessage message => RetransmitRequestMessage.encode message
  | .retransmitRejectMessage message => RetransmitRejectMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (InstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.instrumentDefinitionMessage message, rest)
  else if tag = 11 then (IndexDefinitionMessage.decode bytes).map fun (message, rest) => (.indexDefinitionMessage message, rest)
  else if tag = 14 then (InstrumentInfoMessage.decode bytes).map fun (message, rest) => (.instrumentInfoMessage message, rest)
  else if tag = 15 then (InstrumentRefMessage.decode bytes).map fun (message, rest) => (.instrumentRefMessage message, rest)
  else if tag = 16 then (InstrumentStatusUpdateMessage.decode bytes).map fun (message, rest) => (.instrumentStatusUpdateMessage message, rest)
  else if tag = 20 then (BidPutMessage.decode bytes).map fun (message, rest) => (.bidPutMessage message, rest)
  else if tag = 21 then (AskPutMessage.decode bytes).map fun (message, rest) => (.askPutMessage message, rest)
  else if tag = 22 then (BidQtyReducedMessage.decode bytes).map fun (message, rest) => (.bidQtyReducedMessage message, rest)
  else if tag = 23 then (AskQtyReducedMessage.decode bytes).map fun (message, rest) => (.askQtyReducedMessage message, rest)
  else if tag = 24 then (BidDeleteMessage.decode bytes).map fun (message, rest) => (.bidDeleteMessage message, rest)
  else if tag = 25 then (AskDeleteMessage.decode bytes).map fun (message, rest) => (.askDeleteMessage message, rest)
  else if tag = 30 then (TradeSummaryMessage.decode bytes).map fun (message, rest) => (.tradeSummaryMessage message, rest)
  else if tag = 31 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 33 then (BlockTradeMessage.decode bytes).map fun (message, rest) => (.blockTradeMessage message, rest)
  else if tag = 100 then (SnapshotHeaderMessage.decode bytes).map fun (message, rest) => (.snapshotHeaderMessage message, rest)
  else if tag = 101 then (SnapshotTrailerMessage.decode bytes).map fun (message, rest) => (.snapshotTrailerMessage message, rest)
  else if tag = 119 then (EndOfCycleMessage.decode bytes).map fun (message, rest) => (.endOfCycleMessage message, rest)
  else if tag = 200 then (RetransmitRequestMessage.decode bytes).map fun (message, rest) => (.retransmitRequestMessage message, rest)
  else if tag = 202 then (RetransmitRejectMessage.decode bytes).map fun (message, rest) => (.retransmitRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Md Message: the body, which the record carries with the proof it fits its frame -/
structure MdMessageBody where
  schemaVersion : BitVec 16
  messageFlags : BitVec 16
  transactTime : BitVec 64
  payload : Payload
  padding : Capped 65533
  deriving DecidableEq, Repr

namespace MdMessageBody

def encodeBody (message : MdMessageBody) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaVersion
    ++ (encodeUIntLE 2 message.messageFlags
    ++ (encodeUIntLE 8 message.transactTime
    ++ (Payload.encode message.payload
    ++ (message.padding.val)))))

def decodeBody (bytes : List UInt8) : Option MdMessageBody := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaVersion, bytes) ← decodeUIntLE 2 bytes
  let (messageFlags, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65533 then
    pure { schemaVersion, messageFlags, transactTime, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : MdMessageBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.padding.length_le]
  rfl

end MdMessageBody

/-- Md Message: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev MdMessage := Fitting MdMessageBody.encodeBody 2 65536

namespace MdMessage

def encode (message : MdMessage) : List UInt8 :=
  encodeFramedLE 2 2 MdMessageBody.encodeBody message.val

def decode : List UInt8 → Option (MdMessage × List UInt8) :=
  decodeFittingAllLE 2 2 MdMessageBody.encodeBody MdMessageBody.decodeBody

@[simp] theorem decode_encode (message : MdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 2 MdMessageBody.encodeBody MdMessageBody.decodeBody message (MdMessageBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : MdMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : MdMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
  omega

end MdMessage

/-- Packet -/
structure Packet where
  sendingTime : BitVec 64
  seqNum : BitVec 64
  channelId : BitVec 32
  packetType : BitVec 16
  mdMessage : Bounded 2 MdMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.seqNum
    ++ (encodeUIntLE 4 message.channelId
    ++ (encodeUIntLE 2 message.packetType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.mdMessage.val.length)
    ++ (encodeMany MdMessage.encode message.mdMessage.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (seqNum, bytes) ← decodeUIntLE 8 bytes
  let (channelId, bytes) ← decodeUIntLE 4 bytes
  let (packetType, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (mdMessage_, bytes) ← decodeMany MdMessage.decode messageCount.toNat bytes
  if fits_mdMessage : mdMessage_.length < 256 ^ 2 then
    pure ({ sendingTime, seqNum, channelId, packetType, mdMessage := ⟨mdMessage_, fits_mdMessage⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 4294836249 := by
  have bound_mdMessage := message.mdMessage.length_lt
  have bound_mdMessage_items := encodeMany_length_le MdMessage.encode 65535 MdMessage.encode_length_le message.mdMessage.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 MdMessage.encode MdMessage.decode MdMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdMessage.length_lt]
  rfl

end Packet

end Omi.CoinbaseDeribitMarketdataapiSbeV10
