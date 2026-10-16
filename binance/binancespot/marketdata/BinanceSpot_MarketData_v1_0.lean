import Wire

/-!
# Binance Market Data v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BinanceBinancespotMarketdataSbeV10

/-- Trades Stream Event Message trades Group: 25 bytes -/
structure TradesStreamEventMessageTradesGroup where
  id : BitVec 64
  price : BitVec 64
  qty : BitVec 64
  isBuyerMaker : BitVec 8
  deriving DecidableEq, Repr

namespace TradesStreamEventMessageTradesGroup

def encode (message : TradesStreamEventMessageTradesGroup) : List UInt8 :=
  encodeUIntLE 8 message.id
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.qty
    ++ (encodeUInt 1 message.isBuyerMaker)))

def decode (bytes : List UInt8) : Option (TradesStreamEventMessageTradesGroup × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 8 bytes
  let (isBuyerMaker, bytes) ← decodeUInt 1 bytes
  pure ({ id, price, qty, isBuyerMaker }, bytes)

@[simp] theorem encode_length (message : TradesStreamEventMessageTradesGroup) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradesStreamEventMessageTradesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradesStreamEventMessageTradesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradesStreamEventMessageTradesGroup

/-- Trades Stream Event Message trades Groups -/
structure TradesStreamEventMessageTradesGroups where
  blockLength : BitVec 16
  tradesStreamEventMessageTradesGroup : Bounded 4 TradesStreamEventMessageTradesGroup
  deriving DecidableEq, Repr

namespace TradesStreamEventMessageTradesGroups

def encode (message : TradesStreamEventMessageTradesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.tradesStreamEventMessageTradesGroup.val.length)
    ++ (encodeMany TradesStreamEventMessageTradesGroup.encode message.tradesStreamEventMessageTradesGroup.val))

def decode (bytes : List UInt8) : Option (TradesStreamEventMessageTradesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint32, bytes) ← decodeUIntLE 4 bytes
  let (tradesStreamEventMessageTradesGroup_, bytes) ← decodeMany TradesStreamEventMessageTradesGroup.decode numInGroupUint32.toNat bytes
  if fits_tradesStreamEventMessageTradesGroup : tradesStreamEventMessageTradesGroup_.length < 256 ^ 4 then
    pure ({ blockLength, tradesStreamEventMessageTradesGroup := ⟨tradesStreamEventMessageTradesGroup_, fits_tradesStreamEventMessageTradesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradesStreamEventMessageTradesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradesStreamEventMessageTradesGroups) : (encode message).length ≤ 107374182381 := by
  have bound_tradesStreamEventMessageTradesGroup := message.tradesStreamEventMessageTradesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const TradesStreamEventMessageTradesGroup.encode 25 TradesStreamEventMessageTradesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradesStreamEventMessageTradesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 TradesStreamEventMessageTradesGroup.encode TradesStreamEventMessageTradesGroup.decode TradesStreamEventMessageTradesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradesStreamEventMessageTradesGroup.length_lt]
  rfl

end TradesStreamEventMessageTradesGroups

/-- Symbol -/
structure Symbol where
  symbolData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Symbol

def encode (message : Symbol) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.symbolData.val.length)
    ++ (encodeMany Byte.encode message.symbolData.val)

def decode (bytes : List UInt8) : Option (Symbol × List UInt8) := do
  let (symbolLength, bytes) ← decodeUInt 1 bytes
  let (symbolData_, bytes) ← decodeMany Byte.decode symbolLength.toNat bytes
  if fits_symbolData : symbolData_.length < 256 ^ 1 then
    pure ({ symbolData := ⟨symbolData_, fits_symbolData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Symbol) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Symbol) : (encode message).length ≤ 256 := by
  have bound_symbolData := message.symbolData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Symbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.symbolData.length_lt]
  rfl

end Symbol

/-- Trades Stream Event Message -/
structure TradesStreamEventMessage where
  eventTime : BitVec 64
  transactTime : BitVec 64
  priceExponent : BitVec 8
  qtyExponent : BitVec 8
  tradesStreamEventMessageTradesGroups : TradesStreamEventMessageTradesGroups
  symbol : Symbol
  deriving DecidableEq, Repr

namespace TradesStreamEventMessage

def encode (message : TradesStreamEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUInt 1 message.priceExponent
    ++ (encodeUInt 1 message.qtyExponent
    ++ (TradesStreamEventMessageTradesGroups.encode message.tradesStreamEventMessageTradesGroups
    ++ (Symbol.encode message.symbol)))))

def decode (bytes : List UInt8) : Option (TradesStreamEventMessage × List UInt8) := do
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (priceExponent, bytes) ← decodeUInt 1 bytes
  let (qtyExponent, bytes) ← decodeUInt 1 bytes
  let (tradesStreamEventMessageTradesGroups, bytes) ← TradesStreamEventMessageTradesGroups.decode bytes
  let (symbol, bytes) ← Symbol.decode bytes
  pure ({ eventTime, transactTime, priceExponent, qtyExponent, tradesStreamEventMessageTradesGroups, symbol }, bytes)

theorem encode_length_pos (message : TradesStreamEventMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradesStreamEventMessage) : (encode message).length ≤ 107374182655 := by
  have bound_tradesStreamEventMessageTradesGroups := TradesStreamEventMessageTradesGroups.encode_length_le message.tradesStreamEventMessageTradesGroups
  have bound_symbol := Symbol.encode_length_le message.symbol
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : TradesStreamEventMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradesStreamEventMessageTradesGroups.decode_encode, some_bind]
  dsimp only
  rw [Symbol.decode_encode, some_bind]
  rfl

end TradesStreamEventMessage

/-- Best Bid Ask Stream Event Message -/
structure BestBidAskStreamEventMessage where
  eventTime : BitVec 64
  bookUpdateId : BitVec 64
  priceExponent : BitVec 8
  qtyExponent : BitVec 8
  bidPrice : BitVec 64
  bidQty : BitVec 64
  askPrice : BitVec 64
  askQty : BitVec 64
  symbol : Symbol
  deriving DecidableEq, Repr

namespace BestBidAskStreamEventMessage

def encode (message : BestBidAskStreamEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 8 message.bookUpdateId
    ++ (encodeUInt 1 message.priceExponent
    ++ (encodeUInt 1 message.qtyExponent
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 8 message.bidQty
    ++ (encodeUIntLE 8 message.askPrice
    ++ (encodeUIntLE 8 message.askQty
    ++ (Symbol.encode message.symbol))))))))

def decode (bytes : List UInt8) : Option (BestBidAskStreamEventMessage × List UInt8) := do
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (bookUpdateId, bytes) ← decodeUIntLE 8 bytes
  let (priceExponent, bytes) ← decodeUInt 1 bytes
  let (qtyExponent, bytes) ← decodeUInt 1 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bidQty, bytes) ← decodeUIntLE 8 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (askQty, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Symbol.decode bytes
  pure ({ eventTime, bookUpdateId, priceExponent, qtyExponent, bidPrice, bidQty, askPrice, askQty, symbol }, bytes)

theorem encode_length_pos (message : BestBidAskStreamEventMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BestBidAskStreamEventMessage) : (encode message).length ≤ 306 := by
  have bound_symbol := Symbol.encode_length_le message.symbol
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : BestBidAskStreamEventMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Symbol.decode_encode, some_bind]
  rfl

end BestBidAskStreamEventMessage

/-- Depth Snapshot Stream Event Message bids Group: 16 bytes -/
structure DepthSnapshotStreamEventMessageBidsGroup where
  price : BitVec 64
  qty : BitVec 64
  deriving DecidableEq, Repr

namespace DepthSnapshotStreamEventMessageBidsGroup

def encode (message : DepthSnapshotStreamEventMessageBidsGroup) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.qty)

def decode (bytes : List UInt8) : Option (DepthSnapshotStreamEventMessageBidsGroup × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, qty }, bytes)

@[simp] theorem encode_length (message : DepthSnapshotStreamEventMessageBidsGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DepthSnapshotStreamEventMessageBidsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepthSnapshotStreamEventMessageBidsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DepthSnapshotStreamEventMessageBidsGroup

/-- Depth Snapshot Stream Event Message bids Groups -/
structure DepthSnapshotStreamEventMessageBidsGroups where
  blockLength : BitVec 16
  depthSnapshotStreamEventMessageBidsGroup : Bounded 2 DepthSnapshotStreamEventMessageBidsGroup
  deriving DecidableEq, Repr

namespace DepthSnapshotStreamEventMessageBidsGroups

def encode (message : DepthSnapshotStreamEventMessageBidsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.depthSnapshotStreamEventMessageBidsGroup.val.length)
    ++ (encodeMany DepthSnapshotStreamEventMessageBidsGroup.encode message.depthSnapshotStreamEventMessageBidsGroup.val))

def decode (bytes : List UInt8) : Option (DepthSnapshotStreamEventMessageBidsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint16, bytes) ← decodeUIntLE 2 bytes
  let (depthSnapshotStreamEventMessageBidsGroup_, bytes) ← decodeMany DepthSnapshotStreamEventMessageBidsGroup.decode numInGroupUint16.toNat bytes
  if fits_depthSnapshotStreamEventMessageBidsGroup : depthSnapshotStreamEventMessageBidsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, depthSnapshotStreamEventMessageBidsGroup := ⟨depthSnapshotStreamEventMessageBidsGroup_, fits_depthSnapshotStreamEventMessageBidsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthSnapshotStreamEventMessageBidsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthSnapshotStreamEventMessageBidsGroups) : (encode message).length ≤ 1048564 := by
  have bound_depthSnapshotStreamEventMessageBidsGroup := message.depthSnapshotStreamEventMessageBidsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const DepthSnapshotStreamEventMessageBidsGroup.encode 16 DepthSnapshotStreamEventMessageBidsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthSnapshotStreamEventMessageBidsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 DepthSnapshotStreamEventMessageBidsGroup.encode DepthSnapshotStreamEventMessageBidsGroup.decode DepthSnapshotStreamEventMessageBidsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.depthSnapshotStreamEventMessageBidsGroup.length_lt]
  rfl

end DepthSnapshotStreamEventMessageBidsGroups

/-- Depth Snapshot Stream Event Message asks Group: 16 bytes -/
structure DepthSnapshotStreamEventMessageAsksGroup where
  price : BitVec 64
  qty : BitVec 64
  deriving DecidableEq, Repr

namespace DepthSnapshotStreamEventMessageAsksGroup

def encode (message : DepthSnapshotStreamEventMessageAsksGroup) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.qty)

def decode (bytes : List UInt8) : Option (DepthSnapshotStreamEventMessageAsksGroup × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, qty }, bytes)

@[simp] theorem encode_length (message : DepthSnapshotStreamEventMessageAsksGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DepthSnapshotStreamEventMessageAsksGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepthSnapshotStreamEventMessageAsksGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DepthSnapshotStreamEventMessageAsksGroup

/-- Depth Snapshot Stream Event Message asks Groups -/
structure DepthSnapshotStreamEventMessageAsksGroups where
  blockLength : BitVec 16
  depthSnapshotStreamEventMessageAsksGroup : Bounded 2 DepthSnapshotStreamEventMessageAsksGroup
  deriving DecidableEq, Repr

namespace DepthSnapshotStreamEventMessageAsksGroups

def encode (message : DepthSnapshotStreamEventMessageAsksGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.depthSnapshotStreamEventMessageAsksGroup.val.length)
    ++ (encodeMany DepthSnapshotStreamEventMessageAsksGroup.encode message.depthSnapshotStreamEventMessageAsksGroup.val))

def decode (bytes : List UInt8) : Option (DepthSnapshotStreamEventMessageAsksGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint16, bytes) ← decodeUIntLE 2 bytes
  let (depthSnapshotStreamEventMessageAsksGroup_, bytes) ← decodeMany DepthSnapshotStreamEventMessageAsksGroup.decode numInGroupUint16.toNat bytes
  if fits_depthSnapshotStreamEventMessageAsksGroup : depthSnapshotStreamEventMessageAsksGroup_.length < 256 ^ 2 then
    pure ({ blockLength, depthSnapshotStreamEventMessageAsksGroup := ⟨depthSnapshotStreamEventMessageAsksGroup_, fits_depthSnapshotStreamEventMessageAsksGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthSnapshotStreamEventMessageAsksGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthSnapshotStreamEventMessageAsksGroups) : (encode message).length ≤ 1048564 := by
  have bound_depthSnapshotStreamEventMessageAsksGroup := message.depthSnapshotStreamEventMessageAsksGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const DepthSnapshotStreamEventMessageAsksGroup.encode 16 DepthSnapshotStreamEventMessageAsksGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthSnapshotStreamEventMessageAsksGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 DepthSnapshotStreamEventMessageAsksGroup.encode DepthSnapshotStreamEventMessageAsksGroup.decode DepthSnapshotStreamEventMessageAsksGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.depthSnapshotStreamEventMessageAsksGroup.length_lt]
  rfl

end DepthSnapshotStreamEventMessageAsksGroups

/-- Depth Snapshot Stream Event Message -/
structure DepthSnapshotStreamEventMessage where
  eventTime : BitVec 64
  bookUpdateId : BitVec 64
  priceExponent : BitVec 8
  qtyExponent : BitVec 8
  depthSnapshotStreamEventMessageBidsGroups : DepthSnapshotStreamEventMessageBidsGroups
  depthSnapshotStreamEventMessageAsksGroups : DepthSnapshotStreamEventMessageAsksGroups
  symbol : Symbol
  deriving DecidableEq, Repr

namespace DepthSnapshotStreamEventMessage

def encode (message : DepthSnapshotStreamEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 8 message.bookUpdateId
    ++ (encodeUInt 1 message.priceExponent
    ++ (encodeUInt 1 message.qtyExponent
    ++ (DepthSnapshotStreamEventMessageBidsGroups.encode message.depthSnapshotStreamEventMessageBidsGroups
    ++ (DepthSnapshotStreamEventMessageAsksGroups.encode message.depthSnapshotStreamEventMessageAsksGroups
    ++ (Symbol.encode message.symbol))))))

def decode (bytes : List UInt8) : Option (DepthSnapshotStreamEventMessage × List UInt8) := do
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (bookUpdateId, bytes) ← decodeUIntLE 8 bytes
  let (priceExponent, bytes) ← decodeUInt 1 bytes
  let (qtyExponent, bytes) ← decodeUInt 1 bytes
  let (depthSnapshotStreamEventMessageBidsGroups, bytes) ← DepthSnapshotStreamEventMessageBidsGroups.decode bytes
  let (depthSnapshotStreamEventMessageAsksGroups, bytes) ← DepthSnapshotStreamEventMessageAsksGroups.decode bytes
  let (symbol, bytes) ← Symbol.decode bytes
  pure ({ eventTime, bookUpdateId, priceExponent, qtyExponent, depthSnapshotStreamEventMessageBidsGroups, depthSnapshotStreamEventMessageAsksGroups, symbol }, bytes)

theorem encode_length_pos (message : DepthSnapshotStreamEventMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthSnapshotStreamEventMessage) : (encode message).length ≤ 2097402 := by
  have bound_depthSnapshotStreamEventMessageBidsGroups := DepthSnapshotStreamEventMessageBidsGroups.encode_length_le message.depthSnapshotStreamEventMessageBidsGroups
  have bound_depthSnapshotStreamEventMessageAsksGroups := DepthSnapshotStreamEventMessageAsksGroups.encode_length_le message.depthSnapshotStreamEventMessageAsksGroups
  have bound_symbol := Symbol.encode_length_le message.symbol
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DepthSnapshotStreamEventMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, DepthSnapshotStreamEventMessageBidsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DepthSnapshotStreamEventMessageAsksGroups.decode_encode, some_bind]
  dsimp only
  rw [Symbol.decode_encode, some_bind]
  rfl

end DepthSnapshotStreamEventMessage

/-- Depth Diff Stream Event Message bids Group: 16 bytes -/
structure DepthDiffStreamEventMessageBidsGroup where
  price : BitVec 64
  qty : BitVec 64
  deriving DecidableEq, Repr

namespace DepthDiffStreamEventMessageBidsGroup

def encode (message : DepthDiffStreamEventMessageBidsGroup) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.qty)

def decode (bytes : List UInt8) : Option (DepthDiffStreamEventMessageBidsGroup × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, qty }, bytes)

@[simp] theorem encode_length (message : DepthDiffStreamEventMessageBidsGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DepthDiffStreamEventMessageBidsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepthDiffStreamEventMessageBidsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DepthDiffStreamEventMessageBidsGroup

/-- Depth Diff Stream Event Message bids Groups -/
structure DepthDiffStreamEventMessageBidsGroups where
  blockLength : BitVec 16
  depthDiffStreamEventMessageBidsGroup : Bounded 2 DepthDiffStreamEventMessageBidsGroup
  deriving DecidableEq, Repr

namespace DepthDiffStreamEventMessageBidsGroups

def encode (message : DepthDiffStreamEventMessageBidsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.depthDiffStreamEventMessageBidsGroup.val.length)
    ++ (encodeMany DepthDiffStreamEventMessageBidsGroup.encode message.depthDiffStreamEventMessageBidsGroup.val))

def decode (bytes : List UInt8) : Option (DepthDiffStreamEventMessageBidsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint16, bytes) ← decodeUIntLE 2 bytes
  let (depthDiffStreamEventMessageBidsGroup_, bytes) ← decodeMany DepthDiffStreamEventMessageBidsGroup.decode numInGroupUint16.toNat bytes
  if fits_depthDiffStreamEventMessageBidsGroup : depthDiffStreamEventMessageBidsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, depthDiffStreamEventMessageBidsGroup := ⟨depthDiffStreamEventMessageBidsGroup_, fits_depthDiffStreamEventMessageBidsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthDiffStreamEventMessageBidsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthDiffStreamEventMessageBidsGroups) : (encode message).length ≤ 1048564 := by
  have bound_depthDiffStreamEventMessageBidsGroup := message.depthDiffStreamEventMessageBidsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const DepthDiffStreamEventMessageBidsGroup.encode 16 DepthDiffStreamEventMessageBidsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthDiffStreamEventMessageBidsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 DepthDiffStreamEventMessageBidsGroup.encode DepthDiffStreamEventMessageBidsGroup.decode DepthDiffStreamEventMessageBidsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.depthDiffStreamEventMessageBidsGroup.length_lt]
  rfl

end DepthDiffStreamEventMessageBidsGroups

/-- Depth Diff Stream Event Message asks Group: 16 bytes -/
structure DepthDiffStreamEventMessageAsksGroup where
  price : BitVec 64
  qty : BitVec 64
  deriving DecidableEq, Repr

namespace DepthDiffStreamEventMessageAsksGroup

def encode (message : DepthDiffStreamEventMessageAsksGroup) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.qty)

def decode (bytes : List UInt8) : Option (DepthDiffStreamEventMessageAsksGroup × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, qty }, bytes)

@[simp] theorem encode_length (message : DepthDiffStreamEventMessageAsksGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DepthDiffStreamEventMessageAsksGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepthDiffStreamEventMessageAsksGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DepthDiffStreamEventMessageAsksGroup

/-- Depth Diff Stream Event Message asks Groups -/
structure DepthDiffStreamEventMessageAsksGroups where
  blockLength : BitVec 16
  depthDiffStreamEventMessageAsksGroup : Bounded 2 DepthDiffStreamEventMessageAsksGroup
  deriving DecidableEq, Repr

namespace DepthDiffStreamEventMessageAsksGroups

def encode (message : DepthDiffStreamEventMessageAsksGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.depthDiffStreamEventMessageAsksGroup.val.length)
    ++ (encodeMany DepthDiffStreamEventMessageAsksGroup.encode message.depthDiffStreamEventMessageAsksGroup.val))

def decode (bytes : List UInt8) : Option (DepthDiffStreamEventMessageAsksGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint16, bytes) ← decodeUIntLE 2 bytes
  let (depthDiffStreamEventMessageAsksGroup_, bytes) ← decodeMany DepthDiffStreamEventMessageAsksGroup.decode numInGroupUint16.toNat bytes
  if fits_depthDiffStreamEventMessageAsksGroup : depthDiffStreamEventMessageAsksGroup_.length < 256 ^ 2 then
    pure ({ blockLength, depthDiffStreamEventMessageAsksGroup := ⟨depthDiffStreamEventMessageAsksGroup_, fits_depthDiffStreamEventMessageAsksGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthDiffStreamEventMessageAsksGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthDiffStreamEventMessageAsksGroups) : (encode message).length ≤ 1048564 := by
  have bound_depthDiffStreamEventMessageAsksGroup := message.depthDiffStreamEventMessageAsksGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const DepthDiffStreamEventMessageAsksGroup.encode 16 DepthDiffStreamEventMessageAsksGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthDiffStreamEventMessageAsksGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 DepthDiffStreamEventMessageAsksGroup.encode DepthDiffStreamEventMessageAsksGroup.decode DepthDiffStreamEventMessageAsksGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.depthDiffStreamEventMessageAsksGroup.length_lt]
  rfl

end DepthDiffStreamEventMessageAsksGroups

/-- Depth Diff Stream Event Message -/
structure DepthDiffStreamEventMessage where
  eventTime : BitVec 64
  firstBookUpdateId : BitVec 64
  lastBookUpdateId : BitVec 64
  priceExponent : BitVec 8
  qtyExponent : BitVec 8
  depthDiffStreamEventMessageBidsGroups : DepthDiffStreamEventMessageBidsGroups
  depthDiffStreamEventMessageAsksGroups : DepthDiffStreamEventMessageAsksGroups
  symbol : Symbol
  deriving DecidableEq, Repr

namespace DepthDiffStreamEventMessage

def encode (message : DepthDiffStreamEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.eventTime
    ++ (encodeUIntLE 8 message.firstBookUpdateId
    ++ (encodeUIntLE 8 message.lastBookUpdateId
    ++ (encodeUInt 1 message.priceExponent
    ++ (encodeUInt 1 message.qtyExponent
    ++ (DepthDiffStreamEventMessageBidsGroups.encode message.depthDiffStreamEventMessageBidsGroups
    ++ (DepthDiffStreamEventMessageAsksGroups.encode message.depthDiffStreamEventMessageAsksGroups
    ++ (Symbol.encode message.symbol)))))))

def decode (bytes : List UInt8) : Option (DepthDiffStreamEventMessage × List UInt8) := do
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  let (firstBookUpdateId, bytes) ← decodeUIntLE 8 bytes
  let (lastBookUpdateId, bytes) ← decodeUIntLE 8 bytes
  let (priceExponent, bytes) ← decodeUInt 1 bytes
  let (qtyExponent, bytes) ← decodeUInt 1 bytes
  let (depthDiffStreamEventMessageBidsGroups, bytes) ← DepthDiffStreamEventMessageBidsGroups.decode bytes
  let (depthDiffStreamEventMessageAsksGroups, bytes) ← DepthDiffStreamEventMessageAsksGroups.decode bytes
  let (symbol, bytes) ← Symbol.decode bytes
  pure ({ eventTime, firstBookUpdateId, lastBookUpdateId, priceExponent, qtyExponent, depthDiffStreamEventMessageBidsGroups, depthDiffStreamEventMessageAsksGroups, symbol }, bytes)

theorem encode_length_pos (message : DepthDiffStreamEventMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthDiffStreamEventMessage) : (encode message).length ≤ 2097410 := by
  have bound_depthDiffStreamEventMessageBidsGroups := DepthDiffStreamEventMessageBidsGroups.encode_length_le message.depthDiffStreamEventMessageBidsGroups
  have bound_depthDiffStreamEventMessageAsksGroups := DepthDiffStreamEventMessageAsksGroups.encode_length_le message.depthDiffStreamEventMessageAsksGroups
  have bound_symbol := Symbol.encode_length_le message.symbol
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DepthDiffStreamEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, DepthDiffStreamEventMessageBidsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DepthDiffStreamEventMessageAsksGroups.decode_encode, some_bind]
  dsimp only
  rw [Symbol.decode_encode, some_bind]
  rfl

end DepthDiffStreamEventMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | tradesStreamEventMessage (message : TradesStreamEventMessage) -- 10000
  | bestBidAskStreamEventMessage (message : BestBidAskStreamEventMessage) -- 10001
  | depthSnapshotStreamEventMessage (message : DepthSnapshotStreamEventMessage) -- 10002
  | depthDiffStreamEventMessage (message : DepthDiffStreamEventMessage) -- 10003
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .tradesStreamEventMessage _ => 10000
  | .bestBidAskStreamEventMessage _ => 10001
  | .depthSnapshotStreamEventMessage _ => 10002
  | .depthDiffStreamEventMessage _ => 10003

def encode : Payload → List UInt8
  | .tradesStreamEventMessage message => TradesStreamEventMessage.encode message
  | .bestBidAskStreamEventMessage message => BestBidAskStreamEventMessage.encode message
  | .depthSnapshotStreamEventMessage message => DepthSnapshotStreamEventMessage.encode message
  | .depthDiffStreamEventMessage message => DepthDiffStreamEventMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 107374182655 := by
  cases message with
  | tradesStreamEventMessage inner =>
    have bound_inner := TradesStreamEventMessage.encode_length_le inner
    simp only [encode]
    omega
  | bestBidAskStreamEventMessage inner =>
    have bound_inner := BestBidAskStreamEventMessage.encode_length_le inner
    simp only [encode]
    omega
  | depthSnapshotStreamEventMessage inner =>
    have bound_inner := DepthSnapshotStreamEventMessage.encode_length_le inner
    simp only [encode]
    omega
  | depthDiffStreamEventMessage inner =>
    have bound_inner := DepthDiffStreamEventMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10000 then (TradesStreamEventMessage.decode bytes).map fun (message, rest) => (.tradesStreamEventMessage message, rest)
  else if tag = 10001 then (BestBidAskStreamEventMessage.decode bytes).map fun (message, rest) => (.bestBidAskStreamEventMessage message, rest)
  else if tag = 10002 then (DepthSnapshotStreamEventMessage.decode bytes).map fun (message, rest) => (.depthSnapshotStreamEventMessage message, rest)
  else if tag = 10003 then (DepthDiffStreamEventMessage.decode bytes).map fun (message, rest) => (.depthDiffStreamEventMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 107374182663 := by
  unfold encode
  cases message.payload with
  | tradesStreamEventMessage inner =>
    have bound_inner := TradesStreamEventMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | bestBidAskStreamEventMessage inner =>
    have bound_inner := BestBidAskStreamEventMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | depthSnapshotStreamEventMessage inner =>
    have bound_inner := DepthSnapshotStreamEventMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | depthDiffStreamEventMessage inner =>
    have bound_inner := DepthDiffStreamEventMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Frame -/
structure Frame where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace Frame

def encode (message : Frame) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (Frame × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : Frame) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : Frame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end Frame

end Omi.BinanceBinancespotMarketdataSbeV10
