import Omi.Wire

/-!
# Japan Exchange Group Genium Inet v5.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not the integer that leads it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxOsederivativesGeniuminetOuchV50Client

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
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end DebugPacket

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ Alpha.encode message.password
    ++ Alpha.encode message.requestedSession
    ++ Alpha.encode message.requestedSequenceNumber

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LoginRequestPacket

/-- Enter Order: 96 bytes -/
structure EnterOrder where
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 16
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  deriving DecidableEq, Repr

namespace EnterOrder

def encode (message : EnterOrder) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.openClose
    ++ Alpha.encode message.clientAccount
    ++ Alpha.encode message.customerInfo
    ++ Alpha.encode message.exchangeInfo

def decode (bytes : List UInt8) : Option (EnterOrder × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  pure ({ orderToken, orderBookId, side, quantity, price, timeInForce, openClose, clientAccount, customerInfo, exchangeInfo }, bytes)

@[simp] theorem encode_length (message : EnterOrder) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : EnterOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Side.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end EnterOrder

/-- Enter Mm Order: 79 bytes -/
structure EnterMmOrder where
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  quantity : BitVec 64
  price : BitVec 32
  clientAccount : Alpha 16
  exchangeInfo : Alpha 32
  deriving DecidableEq, Repr

namespace EnterMmOrder

def encode (message : EnterMmOrder) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ Alpha.encode message.clientAccount
    ++ Alpha.encode message.exchangeInfo

def decode (bytes : List UInt8) : Option (EnterMmOrder × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  pure ({ orderToken, orderBookId, side, quantity, price, clientAccount, exchangeInfo }, bytes)

@[simp] theorem encode_length (message : EnterMmOrder) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : EnterMmOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterMmOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Side.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end EnterMmOrder

/-- Replace Order: 104 bytes -/
structure ReplaceOrder where
  existingOrderToken : Alpha 14
  replacementOrderToken : Alpha 14
  quantity : BitVec 64
  price : BitVec 32
  openClose : BitVec 8
  clientAccount : Alpha 16
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  deriving DecidableEq, Repr

namespace ReplaceOrder

def encode (message : ReplaceOrder) : List UInt8 :=
  Alpha.encode message.existingOrderToken
    ++ Alpha.encode message.replacementOrderToken
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUInt 1 message.openClose
    ++ Alpha.encode message.clientAccount
    ++ Alpha.encode message.customerInfo
    ++ Alpha.encode message.exchangeInfo

def decode (bytes : List UInt8) : Option (ReplaceOrder × List UInt8) := do
  let (existingOrderToken, bytes) ← Alpha.decode 14 bytes
  let (replacementOrderToken, bytes) ← Alpha.decode 14 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  pure ({ existingOrderToken, replacementOrderToken, quantity, price, openClose, clientAccount, customerInfo, exchangeInfo }, bytes)

@[simp] theorem encode_length (message : ReplaceOrder) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ReplaceOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ReplaceOrder

/-- Cancel Order: 14 bytes -/
structure CancelOrder where
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace CancelOrder

def encode (message : CancelOrder) : List UInt8 :=
  Alpha.encode message.orderToken

def decode (bytes : List UInt8) : Option (CancelOrder × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ orderToken }, bytes)

@[simp] theorem encode_length (message : CancelOrder) : (encode message).length = 14 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CancelOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end CancelOrder

/-- Cancel By Order Id: 13 bytes -/
structure CancelByOrderId where
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace CancelByOrderId

def encode (message : CancelByOrderId) : List UInt8 :=
  encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.orderId

def decode (bytes : List UInt8) : Option (CancelByOrderId × List UInt8) := do
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ orderBookId, side, orderId }, bytes)

@[simp] theorem encode_length (message : CancelByOrderId) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : CancelByOrderId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelByOrderId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Side.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end CancelByOrderId

/-- Mass Cancel: 35 bytes -/
structure MassCancel where
  orderToken : Alpha 14
  underlyingId : BitVec 32
  scope : BitVec 8
  clientAccount : Alpha 16
  deriving DecidableEq, Repr

namespace MassCancel

def encode (message : MassCancel) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ encodeUInt 4 message.underlyingId
    ++ encodeUInt 1 message.scope
    ++ Alpha.encode message.clientAccount

def decode (bytes : List UInt8) : Option (MassCancel × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (underlyingId, bytes) ← decodeUInt 4 bytes
  let (scope, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  pure ({ orderToken, underlyingId, scope, clientAccount }, bytes)

@[simp] theorem encode_length (message : MassCancel) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MassCancel

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrder (message : EnterOrder) -- 'O' 0x4F
  | enterMmOrder (message : EnterMmOrder) -- 'P' 0x50
  | replaceOrder (message : ReplaceOrder) -- 'U' 0x55
  | cancelOrder (message : CancelOrder) -- 'X' 0x58
  | cancelByOrderId (message : CancelByOrderId) -- 'Y' 0x59
  | massCancel (message : MassCancel) -- 'M' 0x4D
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrder _ => 79
  | .enterMmOrder _ => 80
  | .replaceOrder _ => 85
  | .cancelOrder _ => 88
  | .cancelByOrderId _ => 89
  | .massCancel _ => 77

def encode : UnsequencedMessage → List UInt8
  | .enterOrder message => EnterOrder.encode message
  | .enterMmOrder message => EnterMmOrder.encode message
  | .replaceOrder message => ReplaceOrder.encode message
  | .cancelOrder message => CancelOrder.encode message
  | .cancelByOrderId message => CancelByOrderId.encode message
  | .massCancel message => MassCancel.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrder.decode bytes).map fun (message, rest) => (.enterOrder message, rest)
  else if tag = 80 then (EnterMmOrder.decode bytes).map fun (message, rest) => (.enterMmOrder message, rest)
  else if tag = 85 then (ReplaceOrder.decode bytes).map fun (message, rest) => (.replaceOrder message, rest)
  else if tag = 88 then (CancelOrder.decode bytes).map fun (message, rest) => (.cancelOrder message, rest)
  else if tag = 89 then (CancelByOrderId.decode bytes).map fun (message, rest) => (.cancelByOrderId message, rest)
  else if tag = 77 then (MassCancel.decode bytes).map fun (message, rest) => (.massCancel message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ UnsequencedMessage.encode message.unsequencedMessage

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 105 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrder inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrder.encode_length]
    omega
  | enterMmOrder inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterMmOrder.encode_length]
    omega
  | replaceOrder inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReplaceOrder.encode_length]
    omega
  | cancelOrder inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrder.encode_length]
    omega
  | cancelByOrderId inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelByOrderId.encode_length]
    omega
  | massCancel inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancel.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [UnsequencedMessage.decode_encode, Option.bind_some]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- 'L' 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- 'U' 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- 'R' 0x52
  | logoutRequest (message : LogoutRequest) -- 'O' 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeat.decode bytes).map fun (message, rest) => (.clientHeartbeat message, rest)
  else if tag = 79 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ ClientPayload.encode message.clientPayload

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [ClientPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | debugPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
    omega
  | clientHeartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LogoutRequest.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), Option.bind_some]
  rfl

end ClientPacket

end Omi.JpxOsederivativesGeniuminetOuchV50Client
