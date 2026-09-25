import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Snapshot v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqUtpSnapshotUtpV30Client

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

/-- Client Heartbeat Packet: 0 bytes -/
structure ClientHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ClientHeartbeatPacket

def encode (_ : ClientHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeatPacket

/-- Logout Request Packet: 0 bytes -/
structure LogoutRequestPacket where
  deriving DecidableEq, Repr

namespace LogoutRequestPacket

def encode (_ : LogoutRequestPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequestPacket

/-- Any Client Tcp Payload, selected by Client Packet Type -/
inductive ClientTcpPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | clientHeartbeatPacket (message : ClientHeartbeatPacket) -- "R" 0x52
  | logoutRequestPacket (message : LogoutRequestPacket) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientTcpPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientTcpPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .clientHeartbeatPacket _ => 82
  | .logoutRequestPacket _ => 79

def encode : ClientTcpPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .clientHeartbeatPacket message => ClientHeartbeatPacket.encode message
  | .logoutRequestPacket message => LogoutRequestPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientTcpPayload) : (encode message).length ≤ 46 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | clientHeartbeatPacket inner =>
    simp only [encode, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [encode, LogoutRequestPacket.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientTcpPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 82 then (ClientHeartbeatPacket.decode bytes).map fun (message, rest) => (.clientHeartbeatPacket message, rest)
  else if tag = 79 then (LogoutRequestPacket.decode bytes).map fun (message, rest) => (.logoutRequestPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ClientTcpPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientTcpPayload

/-- Client Packet -/
structure ClientPacket where
  clientTcpPayload : ClientTcpPayload
  deriving DecidableEq, Repr

namespace ClientPacket

def encodeBody (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientTcpPayload.tag message.clientTcpPayload)
    ++ (ClientTcpPayload.encode message.clientTcpPayload)

def decodeBody (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientTcpPayload, bytes) ← ClientTcpPayload.decode clientPacketType bytes
  pure ({ clientTcpPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientTcpPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientTcpPayload with
  | debugPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | clientHeartbeatPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, LogoutRequestPacket.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientPacket

end Omi.NasdaqUtpSnapshotUtpV30Client
