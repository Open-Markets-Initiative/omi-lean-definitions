import Omi.Wire

/-!
# Bolsa Institucional de Valores Order Entry v1.05

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BivaBivaequitiesOrderentryOuchV105Client

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x43, 0x48, 0x4F, 0x59, 0x4D, 0x53]

inductive AccountType where
  | client -- Client
  | house -- House
  | other -- Other
  | strategy -- Strategy
  | marketMaker -- Market Maker
  | stabilisation -- Stabilisation
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .client => 0x43
  | .house => 0x48
  | .other => 0x4F
  | .strategy => 0x59
  | .marketMaker => 0x4D
  | .stabilisation => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x43 then .client
  else if byte = 0x48 then .house
  else if byte = 0x4F then .other
  else if byte = 0x59 then .strategy
  else if byte = 0x4D then .marketMaker
  else .stabilisation

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | client => decide
  | house => decide
  | other => decide
  | strategy => decide
  | marketMaker => decide
  | stabilisation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53, 0x54]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | shortSell -- Short Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .shortSell => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .shortSell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | shortSell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

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
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestPacket

/-- Enter Order Message: 42 bytes -/
structure EnterOrderMessage where
  orderToken : BitVec 32
  accountType : AccountType
  accountId : BitVec 32
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 32
  timeInForce : BitVec 32
  clientId : BitVec 32
  minimumQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  encodeUInt 4 message.orderToken
    ++ (AccountType.encode message.accountType
    ++ (encodeUInt 4 message.accountId
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.timeInForce
    ++ (encodeUInt 4 message.clientId
    ++ (encodeUInt 8 message.minimumQuantity)))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← decodeUInt 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (accountId, bytes) ← decodeUInt 4 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 4 bytes
  let (clientId, bytes) ← decodeUInt 4 bytes
  let (minimumQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ orderToken, accountType, accountId, orderVerb, quantity, orderbook, price, timeInForce, clientId, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AccountType.encode_length, OrderVerb.encode_length]

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EnterOrderMessage

/-- Replace Order Message: 20 bytes -/
structure ReplaceOrderMessage where
  existingOrderToken : BitVec 32
  replacementOrderToken : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUInt 4 message.existingOrderToken
    ++ (encodeUInt 4 message.replacementOrderToken
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price)))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (existingOrderToken, bytes) ← decodeUInt 4 bytes
  let (replacementOrderToken, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ existingOrderToken, replacementOrderToken, quantity, price }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 4 bytes -/
structure CancelOrderMessage where
  orderToken : BitVec 32
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUInt 4 message.orderToken

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← decodeUInt 4 bytes
  pure ({ orderToken }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelOrderMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- "U" 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 42 := by
  cases message with
  | enterOrderMessage inner =>
    simp only [encode, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [encode, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
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
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 43 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
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
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- "R" 0x52
  | logoutRequest (message : LogoutRequest) -- "O" 0x4F
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

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 46 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega

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
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
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
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.BivaBivaequitiesOrderentryOuchV105Client
