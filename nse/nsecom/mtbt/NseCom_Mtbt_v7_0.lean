import Omi.Wire

/-!
# National Stock Exchange of India Ltd Multicast Tick By Tick v7.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecomMtbtBinaryV70

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderType where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
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

/-- Stream Header: 8 bytes -/
structure StreamHeader where
  messageLength : BitVec 16
  streamId : BitVec 16
  sequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace StreamHeader

def encode (message : StreamHeader) : List UInt8 :=
  encodeUIntLE 2 message.messageLength
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.sequenceNumber))

def decode (bytes : List UInt8) : Option (StreamHeader × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageLength, streamId, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StreamHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StreamHeader

/-- New Order Message: 29 bytes -/
structure NewOrderMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : NewOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewOrderMessage

/-- Order Modification Message: 29 bytes -/
structure OrderModificationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderModificationMessage

def encode (message : OrderModificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderModificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : OrderModificationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModificationMessage

/-- Order Cancellation Message: 29 bytes -/
structure OrderCancellationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationMessage

def encode (message : OrderCancellationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderCancellationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationMessage

/-- Trade Message: 36 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  buyOrderId : Alpha 8
  sellOrderId : Alpha 8
  token : BitVec 32
  tradePrice : BitVec 32
  tradeQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.buyOrderId
    ++ (Alpha.encode message.sellOrderId
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.tradeQuantity)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← Alpha.decode 8 bytes
  let (sellOrderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (tradeQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, buyOrderId, sellOrderId, token, tradePrice, tradeQuantity }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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

end TradeMessage

/-- New Spread Order Message: 29 bytes -/
structure NewSpreadOrderMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace NewSpreadOrderMessage

def encode (message : NewSpreadOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (NewSpreadOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : NewSpreadOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : NewSpreadOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewSpreadOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewSpreadOrderMessage

/-- Spread Order Modification Message: 29 bytes -/
structure SpreadOrderModificationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadOrderModificationMessage

def encode (message : SpreadOrderModificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadOrderModificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadOrderModificationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : SpreadOrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadOrderModificationMessage

/-- Spread Order Cancellation Message: 29 bytes -/
structure SpreadOrderCancellationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadOrderCancellationMessage

def encode (message : SpreadOrderCancellationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadOrderCancellationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadOrderCancellationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : SpreadOrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadOrderCancellationMessage

/-- Spread Trade Message: 36 bytes -/
structure SpreadTradeMessage where
  timestamp : BitVec 64
  buyOrderId : Alpha 8
  sellOrderId : Alpha 8
  token : BitVec 32
  tradePrice : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadTradeMessage

def encode (message : SpreadTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.buyOrderId
    ++ (Alpha.encode message.sellOrderId
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← Alpha.decode 8 bytes
  let (sellOrderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, buyOrderId, sellOrderId, token, tradePrice, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadTradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SpreadTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadTradeMessage) (rest : List UInt8) :
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

end SpreadTradeMessage

/-- Trade Cancel Message: 36 bytes -/
structure TradeCancelMessage where
  timestamp : BitVec 64
  buyOrderId : Alpha 8
  sellOrderId : Alpha 8
  token : BitVec 32
  tradePrice : BitVec 32
  tradeQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.buyOrderId
    ++ (Alpha.encode message.sellOrderId
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.tradeQuantity)))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← Alpha.decode 8 bytes
  let (sellOrderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (tradeQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, buyOrderId, sellOrderId, token, tradePrice, tradeQuantity }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
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

end TradeCancelMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  lastSequenceNo : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSequenceNo

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (lastSequenceNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSequenceNo }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | newOrderMessage (message : NewOrderMessage) -- 'N' 0x4E
  | orderModificationMessage (message : OrderModificationMessage) -- 'M' 0x4D
  | orderCancellationMessage (message : OrderCancellationMessage) -- 'X' 0x58
  | tradeMessage (message : TradeMessage) -- 'T' 0x54
  | newSpreadOrderMessage (message : NewSpreadOrderMessage) -- 'G' 0x47
  | spreadOrderModificationMessage (message : SpreadOrderModificationMessage) -- 'H' 0x48
  | spreadOrderCancellationMessage (message : SpreadOrderCancellationMessage) -- 'J' 0x4A
  | spreadTradeMessage (message : SpreadTradeMessage) -- 'K' 0x4B
  | tradeCancelMessage (message : TradeCancelMessage) -- 'C' 0x43
  | heartbeatMessage (message : HeartbeatMessage) -- 'Z' 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .newOrderMessage _ => 78
  | .orderModificationMessage _ => 77
  | .orderCancellationMessage _ => 88
  | .tradeMessage _ => 84
  | .newSpreadOrderMessage _ => 71
  | .spreadOrderModificationMessage _ => 72
  | .spreadOrderCancellationMessage _ => 74
  | .spreadTradeMessage _ => 75
  | .tradeCancelMessage _ => 67
  | .heartbeatMessage _ => 90

def encode : Payload → List UInt8
  | .newOrderMessage message => NewOrderMessage.encode message
  | .orderModificationMessage message => OrderModificationMessage.encode message
  | .orderCancellationMessage message => OrderCancellationMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .newSpreadOrderMessage message => NewSpreadOrderMessage.encode message
  | .spreadOrderModificationMessage message => SpreadOrderModificationMessage.encode message
  | .spreadOrderCancellationMessage message => SpreadOrderCancellationMessage.encode message
  | .spreadTradeMessage message => SpreadTradeMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 78 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 77 then (OrderModificationMessage.decode bytes).map fun (message, rest) => (.orderModificationMessage message, rest)
  else if tag = 88 then (OrderCancellationMessage.decode bytes).map fun (message, rest) => (.orderCancellationMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 71 then (NewSpreadOrderMessage.decode bytes).map fun (message, rest) => (.newSpreadOrderMessage message, rest)
  else if tag = 72 then (SpreadOrderModificationMessage.decode bytes).map fun (message, rest) => (.spreadOrderModificationMessage message, rest)
  else if tag = 74 then (SpreadOrderCancellationMessage.decode bytes).map fun (message, rest) => (.spreadOrderCancellationMessage message, rest)
  else if tag = 75 then (SpreadTradeMessage.decode bytes).map fun (message, rest) => (.spreadTradeMessage message, rest)
  else if tag = 67 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 90 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  streamHeader : StreamHeader
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  StreamHeader.encode message.streamHeader
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (streamHeader, bytes) ← StreamHeader.decode bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ streamHeader, payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [StreamHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 45 := by
  unfold encode
  cases message.payload with
  | newOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, NewOrderMessage.encode_length]
    omega
  | orderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, OrderModificationMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, OrderCancellationMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | newSpreadOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, NewSpreadOrderMessage.encode_length]
    omega
  | spreadOrderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, SpreadOrderModificationMessage.encode_length]
    omega
  | spreadOrderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, SpreadOrderCancellationMessage.encode_length]
    omega
  | spreadTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, SpreadTradeMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, TradeCancelMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, HeartbeatMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NseNsecomMtbtBinaryV70
