import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewItchV20Udp

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

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

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59]

inductive Display where
  | displayed -- Displayed
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .displayed => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Display :=
  .displayed

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | displayed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Add Order Message: 33 bytes -/
structure AddOrderMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  display : Display
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Display.encode message.display)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (display, bytes) ← Display.decode bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, display }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Display.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 24 bytes -/
structure OrderExecutedMessage where
  orderReferenceNumber : Alpha 9
  executedShares : Alpha 6
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.executedShares
    ++ (Alpha.encode message.matchNumber))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (executedShares, bytes) ← Alpha.decode 6 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ orderReferenceNumber, executedShares, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Cancel Message: 15 bytes -/
structure OrderCancelMessage where
  orderReferenceNumber : Alpha 9
  canceledShares : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.canceledShares)

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (canceledShares, bytes) ← Alpha.decode 6 bytes
  pure ({ orderReferenceNumber, canceledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelMessage

/-- Trade Message: 41 bytes -/
structure TradeMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.matchNumber)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 9 bytes -/
structure BrokenTradeMessage where
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  Alpha.encode message.matchNumber

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderCancelMessage _ => 88
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 41 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  timestamp : Alpha 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ timestamp, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequence : BitVec 32
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 4 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequence, bytes) ← decodeUInt 4 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequence, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNsmequitiesTotalviewItchV20Udp
