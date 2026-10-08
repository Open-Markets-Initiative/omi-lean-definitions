import Wire

/-!
# New York Stock Exchange ArcaBook v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaequitiesArcabookPillarV21

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x4D, 0x48, 0x43]

inductive AuctionType where
  | earlyOpeningAuction -- Early Opening Auction
  | coreOpeningAuction -- Core Opening Auction
  | tradingHaltAuction -- Trading Halt Auction
  | closingAuction -- Closing Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .earlyOpeningAuction => 0x4F
  | .coreOpeningAuction => 0x4D
  | .tradingHaltAuction => 0x48
  | .closingAuction => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .earlyOpeningAuction
  else if byte = 0x4D then .coreOpeningAuction
  else if byte = 0x48 then .tradingHaltAuction
  else .closingAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | earlyOpeningAuction => decide
  | coreOpeningAuction => decide
  | tradingHaltAuction => decide
  | closingAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Send Time: 8 bytes -/
structure SendTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SendTime

def encode (message : SendTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SendTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SendTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SendTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SendTime

/-- Add Order Message: 27 bytes -/
structure AddOrderMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  tradeSession : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.tradeSession))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeSession, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, orderIdgtcIndicator, tradeSession }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMessage

/-- Modify Order Message: 27 bytes -/
structure ModifyOrderMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  reasonCode : BitVec 8
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.reasonCode))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, orderIdgtcIndicator, reasonCode }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrderMessage

/-- Delete Order Message: 19 bytes -/
structure DeleteOrderMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  reasonCode : BitVec 8
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.reasonCode))))))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, orderId, side, orderIdgtcIndicator, reasonCode }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOrderMessage

/-- Execution Message: 30 bytes -/
structure ExecutionMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  orderIdgtcIndicator : BitVec 8
  reasonCode : BitVec 8
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace ExecutionMessage

def encode (message : ExecutionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.reasonCode
    ++ (encodeUIntLE 4 message.tradeId))))))))

def decode (bytes : List UInt8) : Option (ExecutionMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 1 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, orderIdgtcIndicator, reasonCode, tradeId }, bytes)

@[simp] theorem encode_length (message : ExecutionMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionMessage

/-- Imbalance Message: 48 bytes -/
structure ImbalanceMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  indicativeMatchPrice : BitVec 32
  pairedQty : BitVec 32
  totalImbalanceQty : BitVec 32
  marketImbalanceQty : BitVec 32
  auctionTime : BitVec 16
  auctionType : AuctionType
  imbalanceSide : Alpha 1
  continuousBookClearingPrice : BitVec 32
  closingOnlyClearingPrice : BitVec 32
  ssrFilingPrice : BitVec 32
  deriving DecidableEq, Repr

namespace ImbalanceMessage

def encode (message : ImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.indicativeMatchPrice
    ++ (encodeUIntLE 4 message.pairedQty
    ++ (encodeUIntLE 4 message.totalImbalanceQty
    ++ (encodeUIntLE 4 message.marketImbalanceQty
    ++ (encodeUIntLE 2 message.auctionTime
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.continuousBookClearingPrice
    ++ (encodeUIntLE 4 message.closingOnlyClearingPrice
    ++ (encodeUIntLE 4 message.ssrFilingPrice)))))))))))))

def decode (bytes : List UInt8) : Option (ImbalanceMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (indicativeMatchPrice, bytes) ← decodeUIntLE 4 bytes
  let (pairedQty, bytes) ← decodeUIntLE 4 bytes
  let (totalImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (marketImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (auctionTime, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceSide, bytes) ← Alpha.decode 1 bytes
  let (continuousBookClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (closingOnlyClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (ssrFilingPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, indicativeMatchPrice, pairedQty, totalImbalanceQty, marketImbalanceQty, auctionTime, auctionType, imbalanceSide, continuousBookClearingPrice, closingOnlyClearingPrice, ssrFilingPrice }, bytes)

@[simp] theorem encode_length (message : ImbalanceMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ImbalanceMessage

/-- Add Order Refresh Message: 31 bytes -/
structure AddOrderRefreshMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  tradeSession : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderRefreshMessage

def encode (message : AddOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.tradeSession)))))))))

def decode (bytes : List UInt8) : Option (AddOrderRefreshMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeSession, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, orderIdgtcIndicator, tradeSession }, bytes)

@[simp] theorem encode_length (message : AddOrderRefreshMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : AddOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderRefreshMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderRefreshMessage

/-- Attributed Add Order Message: 32 bytes -/
structure AttributedAddOrderMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  tradeSession : BitVec 8
  firmId : BitVec 40
  deriving DecidableEq, Repr

namespace AttributedAddOrderMessage

def encode (message : AttributedAddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.tradeSession
    ++ (encodeUIntLE 5 message.firmId)))))))))

def decode (bytes : List UInt8) : Option (AttributedAddOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeSession, bytes) ← decodeUIntLE 1 bytes
  let (firmId, bytes) ← decodeUIntLE 5 bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, orderIdgtcIndicator, tradeSession, firmId }, bytes)

@[simp] theorem encode_length (message : AttributedAddOrderMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : AttributedAddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AttributedAddOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AttributedAddOrderMessage

/-- Attributed Add Order Refresh Message: 36 bytes -/
structure AttributedAddOrderRefreshMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  side : Side
  orderIdgtcIndicator : BitVec 8
  tradeSession : BitVec 8
  firmId : BitVec 40
  deriving DecidableEq, Repr

namespace AttributedAddOrderRefreshMessage

def encode (message : AttributedAddOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.orderIdgtcIndicator
    ++ (encodeUIntLE 1 message.tradeSession
    ++ (encodeUIntLE 5 message.firmId))))))))))

def decode (bytes : List UInt8) : Option (AttributedAddOrderRefreshMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderIdgtcIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeSession, bytes) ← decodeUIntLE 1 bytes
  let (firmId, bytes) ← decodeUIntLE 5 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, orderIdgtcIndicator, tradeSession, firmId }, bytes)

@[simp] theorem encode_length (message : AttributedAddOrderRefreshMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : AttributedAddOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AttributedAddOrderRefreshMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AttributedAddOrderRefreshMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | addOrderMessage (message : AddOrderMessage) -- 100
  | modifyOrderMessage (message : ModifyOrderMessage) -- 101
  | deleteOrderMessage (message : DeleteOrderMessage) -- 102
  | executionMessage (message : ExecutionMessage) -- 103
  | imbalanceMessage (message : ImbalanceMessage) -- 105
  | addOrderRefreshMessage (message : AddOrderRefreshMessage) -- 106
  | attributedAddOrderMessage (message : AttributedAddOrderMessage) -- 107
  | attributedAddOrderRefreshMessage (message : AttributedAddOrderRefreshMessage) -- 108
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .addOrderMessage _ => 100
  | .modifyOrderMessage _ => 101
  | .deleteOrderMessage _ => 102
  | .executionMessage _ => 103
  | .imbalanceMessage _ => 105
  | .addOrderRefreshMessage _ => 106
  | .attributedAddOrderMessage _ => 107
  | .attributedAddOrderRefreshMessage _ => 108

def encode : Payload → List UInt8
  | .addOrderMessage message => AddOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .executionMessage message => ExecutionMessage.encode message
  | .imbalanceMessage message => ImbalanceMessage.encode message
  | .addOrderRefreshMessage message => AddOrderRefreshMessage.encode message
  | .attributedAddOrderMessage message => AttributedAddOrderMessage.encode message
  | .attributedAddOrderRefreshMessage message => AttributedAddOrderRefreshMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 48 := by
  cases message with
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [encode, DeleteOrderMessage.encode_length]
    omega
  | executionMessage inner =>
    simp only [encode, ExecutionMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [encode, ImbalanceMessage.encode_length]
    omega
  | addOrderRefreshMessage inner =>
    simp only [encode, AddOrderRefreshMessage.encode_length]
    omega
  | attributedAddOrderMessage inner =>
    simp only [encode, AttributedAddOrderMessage.encode_length]
    omega
  | attributedAddOrderRefreshMessage inner =>
    simp only [encode, AttributedAddOrderRefreshMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 101 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 102 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 103 then (ExecutionMessage.decode bytes).map fun (message, rest) => (.executionMessage message, rest)
  else if tag = 105 then (ImbalanceMessage.decode bytes).map fun (message, rest) => (.imbalanceMessage message, rest)
  else if tag = 106 then (AddOrderRefreshMessage.decode bytes).map fun (message, rest) => (.addOrderRefreshMessage message, rest)
  else if tag = 107 then (AttributedAddOrderMessage.decode bytes).map fun (message, rest) => (.attributedAddOrderMessage message, rest)
  else if tag = 108 then (AttributedAddOrderRefreshMessage.decode bytes).map fun (message, rest) => (.attributedAddOrderRefreshMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, DeleteOrderMessage.encode_length]
    omega
  | executionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ExecutionMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ImbalanceMessage.encode_length]
    omega
  | addOrderRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AddOrderRefreshMessage.encode_length]
    omega
  | attributedAddOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AttributedAddOrderMessage.encode_length]
    omega
  | attributedAddOrderRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AttributedAddOrderRefreshMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  deliveryFlag : BitVec 8
  seqNum : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.seqNum
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (numberMsgs, bytes) ← decodeUIntLE 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode numberMsgs.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, deliveryFlag, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
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
  rw [List.append_assoc, SendTime.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NyseArcaequitiesArcabookPillarV21
