import Omi.Wire

/-!
# Eurex Exchange Extended Derivatives Clearing Interface v14.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Heartbeat is not framed: its length Body Len is not the integer that leads it.

Note: Logon Request is not framed: its length Body Len is not the integer that leads it.

Note: Logout Request is not framed: its length Body Len is not the integer that leads it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EdciFbeV141Client

/-- Heartbeat: 2 bytes -/
structure Heartbeat where
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (message : Heartbeat) : List UInt8 :=
  Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2 }, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Heartbeat

/-- Request Header Comp: 8 bytes -/
structure RequestHeaderComp where
  msgSeqNum : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace RequestHeaderComp

def encode (message : RequestHeaderComp) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (RequestHeaderComp × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ msgSeqNum, pad4 }, bytes)

@[simp] theorem encode_length (message : RequestHeaderComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RequestHeaderComp

/-- Logon Request: 82 bytes -/
structure LogonRequest where
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  heartBtInt : BitVec 32
  partyIdSessionId : BitVec 32
  defaultCstmApplVerId : Alpha 30
  password : Alpha 32
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace LogonRequest

def encode (message : LogonRequest) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.heartBtInt
    ++ encodeUIntLE 4 message.partyIdSessionId
    ++ Alpha.encode message.defaultCstmApplVerId
    ++ Alpha.encode message.password
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (LogonRequest × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, requestHeaderComp, heartBtInt, partyIdSessionId, defaultCstmApplVerId, password, pad2v2 }, bytes)

@[simp] theorem encode_length (message : LogonRequest) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LogonRequest

/-- Logout Request: 10 bytes -/
structure LogoutRequest where
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  pure ({ pad2, requestHeaderComp }, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  rfl

end LogoutRequest

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | heartbeat (message : Heartbeat) -- 10011
  | logonRequest (message : LogonRequest) -- 10000
  | logoutRequest (message : LogoutRequest) -- 10002
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .heartbeat _ => 10011
  | .logonRequest _ => 10000
  | .logoutRequest _ => 10002

def encode : ClientPayload → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .logonRequest message => LogonRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 10011 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 10000 then (LogonRequest.decode bytes).map fun (message, rest) => (.logonRequest message, rest)
  else if tag = 10002 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Message -/
structure ClientMessage where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encodeBody (message : ClientMessage) : List UInt8 :=
  encodeUIntLE 2 (ClientPayload.tag message.clientPayload)
    ++ ClientPayload.encode message.clientPayload

def decodeBody (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [ClientPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.clientPayload with
  | heartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | logonRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogonRequest.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogoutRequest.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ClientMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ClientMessage × List UInt8) :=
  decodeFramedLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 4 4 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  clientMessage : List ClientMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientMessage.encode message.clientMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientMessage ← decodeAll ClientMessage.decode bytes.length bytes
  pure { clientMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), Option.bind_some]
  rfl

end ClientPacket

end Omi.EurexT7EdciFbeV141Client
