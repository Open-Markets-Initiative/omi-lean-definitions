import Omi.Wire

/-!
# National Stock Exchange of India Ltd Mtbt Order Book Snapshot Recovery v6.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsefoSnapshotBinaryV69Tcp

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

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | newOrderMessage (message : NewOrderMessage) -- "N" 0x4E
  | newSpreadOrderMessage (message : NewSpreadOrderMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .newOrderMessage _ => 78
  | .newSpreadOrderMessage _ => 71

def encode : Payload → List UInt8
  | .newOrderMessage message => NewOrderMessage.encode message
  | .newSpreadOrderMessage message => NewSpreadOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 29 := by
  cases message with
  | newOrderMessage inner =>
    simp only [encode, NewOrderMessage.encode_length]
    omega
  | newSpreadOrderMessage inner =>
    simp only [encode, NewSpreadOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 78 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 71 then (NewSpreadOrderMessage.decode bytes).map fun (message, rest) => (.newSpreadOrderMessage message, rest)
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

def encode (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 30 := by
  unfold encode
  cases message.payload with
  | newOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewOrderMessage.encode_length]
    omega
  | newSpreadOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewSpreadOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  transCode : BitVec 16
  size : BitVec 32
  lastSequenceNumber : BitVec 32
  streamId : BitVec 16
  message : Bounded 4 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.transCode
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.message.val.length)
    ++ (encodeUIntLE 4 message.lastSequenceNumber
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (transCode, bytes) ← decodeUIntLE 2 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRecords, bytes) ← decodeUIntLE 4 bytes
  let (lastSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode numberOfRecords.toNat bytes
  if fits_message : message_.length < 256 ^ 4 then
    pure ({ transCode, size, lastSequenceNumber, streamId, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 128849018866 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 30 Message.encode_length_le message.message.val
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
  rw [decodeMany_bounded 4 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NseNsefoSnapshotBinaryV69Tcp
