import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewItchV10Server

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfSession -- Start Of Session
  | endOfSession -- End Of Session
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfSession => 0x53
  | .endOfSession => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfSession
  else .endOfSession

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfSession => decide
  | endOfSession => decide
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

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 20 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 10
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 10 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

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

/-- Add Order Message: 46 bytes -/
structure AddOrderMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 9
  stock : Alpha 6
  price : Alpha 20
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
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (display, bytes) ← Display.decode bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, display }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 46 := by
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

/-- Order Executed Message: 31 bytes -/
structure OrderExecutedMessage where
  orderReferenceNumber : Alpha 9
  executedShares : Alpha 9
  matchNumber : Alpha 9
  contraBrokerCode : Alpha 4
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.executedShares
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.contraBrokerCode)))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (executedShares, bytes) ← Alpha.decode 9 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (contraBrokerCode, bytes) ← Alpha.decode 4 bytes
  pure ({ orderReferenceNumber, executedShares, matchNumber, contraBrokerCode }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 31 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Cancel Message: 18 bytes -/
structure OrderCancelMessage where
  orderReferenceNumber : Alpha 9
  canceledShares : Alpha 9
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.canceledShares)

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (canceledShares, bytes) ← Alpha.decode 9 bytes
  pure ({ orderReferenceNumber, canceledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 18 := by
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

/-- Trade Message: 58 bytes -/
structure TradeMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 9
  stock : Alpha 6
  price : Alpha 20
  matchNumber : Alpha 9
  contraBrokerCode : Alpha 4
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.contraBrokerCode))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← Alpha.decode 9 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  let (contraBrokerCode, bytes) ← Alpha.decode 4 bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, matchNumber, contraBrokerCode }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 58 := by
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

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderCancelMessage _ => 88
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 58 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  timestamp : Alpha 7
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 7 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode messageType bytes
  pure ({ timestamp, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 66 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 66 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Packet -/
structure ServerPacket where
  serverPayload : ServerPayload
  soupLf : BitVec 8
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload
    ++ (encodeUInt 1 message.soupLf))

def decode (bytes : List UInt8) : Option (ServerPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  let (soupLf, bytes) ← decodeUInt 1 bytes
  pure ({ serverPayload, soupLf }, bytes)

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerPacket) : (encode message).length ≤ 68 := by
  unfold encode
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ServerPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ServerPayload.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNsmequitiesTotalviewItchV10Server
