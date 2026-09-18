import Omi.Wire

/-!
# Coinbase Session Layer v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseCoinbasederivativesSessionTcpV12

/-- Logon Message: 49 bytes -/
structure LogonMessage where
  username : Alpha 16
  password : Alpha 32
  resetSeqNum : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (encodeUInt 1 message.resetSeqNum))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (resetSeqNum, bytes) ← decodeUInt 1 bytes
  pure ({ username, password, resetSeqNum }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonMessage

/-- Logon Conf Message: 4 bytes -/
structure LogonConfMessage where
  heartbeatIntervalSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace LogonConfMessage

def encode (message : LogonConfMessage) : List UInt8 :=
  encodeUIntLE 4 message.heartbeatIntervalSeconds

def decode (bytes : List UInt8) : Option (LogonConfMessage × List UInt8) := do
  let (heartbeatIntervalSeconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ heartbeatIntervalSeconds }, bytes)

@[simp] theorem encode_length (message : LogonConfMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LogonConfMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonConfMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonConfMessage

/-- Logout Message: 64 bytes -/
structure LogoutMessage where
  reasonString64 : Alpha 64
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Alpha.encode message.reasonString64

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (reasonString64, bytes) ← Alpha.decode 64 bytes
  pure ({ reasonString64 }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Logged Out Message: 64 bytes -/
structure LoggedOutMessage where
  reasonString64 : Alpha 64
  deriving DecidableEq, Repr

namespace LoggedOutMessage

def encode (message : LoggedOutMessage) : List UInt8 :=
  Alpha.encode message.reasonString64

def decode (bytes : List UInt8) : Option (LoggedOutMessage × List UInt8) := do
  let (reasonString64, bytes) ← Alpha.decode 64 bytes
  pure ({ reasonString64 }, bytes)

@[simp] theorem encode_length (message : LoggedOutMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoggedOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoggedOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoggedOutMessage

/-- Heartbeat Message: 8 bytes -/
structure HeartbeatMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 8 := by
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

/-- Test Request Message: 8 bytes -/
structure TestRequestMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace TestRequestMessage

def encode (message : TestRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (TestRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : TestRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TestRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TestRequestMessage

/-- Resend Request Message: 8 bytes -/
structure ResendRequestMessage where
  fromSequenceNumber : BitVec 32
  toSequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace ResendRequestMessage

def encode (message : ResendRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.fromSequenceNumber
    ++ (encodeUIntLE 4 message.toSequenceNumber)

def decode (bytes : List UInt8) : Option (ResendRequestMessage × List UInt8) := do
  let (fromSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (toSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ fromSequenceNumber, toSequenceNumber }, bytes)

@[simp] theorem encode_length (message : ResendRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ResendRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResendRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ResendRequestMessage

/-- Gap Fill Message: 8 bytes -/
structure GapFillMessage where
  newSequenceNumber : BitVec 32
  gapFillPadding : BitVec 32
  deriving DecidableEq, Repr

namespace GapFillMessage

def encode (message : GapFillMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSequenceNumber
    ++ (encodeUIntLE 4 message.gapFillPadding)

def decode (bytes : List UInt8) : Option (GapFillMessage × List UInt8) := do
  let (newSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (gapFillPadding, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSequenceNumber, gapFillPadding }, bytes)

@[simp] theorem encode_length (message : GapFillMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : GapFillMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GapFillMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end GapFillMessage

/-- Reject Message: 72 bytes -/
structure RejectMessage where
  refSequenceNumber : BitVec 32
  reasonRejectReason : BitVec 32
  details : Alpha 64
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.refSequenceNumber
    ++ (encodeUIntLE 4 message.reasonRejectReason
    ++ (Alpha.encode message.details))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (refSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (reasonRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (details, bytes) ← Alpha.decode 64 bytes
  pure ({ refSequenceNumber, reasonRejectReason, details }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 100
  | logonConfMessage (message : LogonConfMessage) -- 200
  | logoutMessage (message : LogoutMessage) -- 101
  | loggedOutMessage (message : LoggedOutMessage) -- 201
  | heartbeatMessage (message : HeartbeatMessage) -- 10
  | testRequestMessage (message : TestRequestMessage) -- 11
  | resendRequestMessage (message : ResendRequestMessage) -- 102
  | gapFillMessage (message : GapFillMessage) -- 202
  | rejectMessage (message : RejectMessage) -- 210
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .logonMessage _ => 100
  | .logonConfMessage _ => 200
  | .logoutMessage _ => 101
  | .loggedOutMessage _ => 201
  | .heartbeatMessage _ => 10
  | .testRequestMessage _ => 11
  | .resendRequestMessage _ => 102
  | .gapFillMessage _ => 202
  | .rejectMessage _ => 210

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logonConfMessage message => LogonConfMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .loggedOutMessage message => LoggedOutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testRequestMessage message => TestRequestMessage.encode message
  | .resendRequestMessage message => ResendRequestMessage.encode message
  | .gapFillMessage message => GapFillMessage.encode message
  | .rejectMessage message => RejectMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 200 then (LogonConfMessage.decode bytes).map fun (message, rest) => (.logonConfMessage message, rest)
  else if tag = 101 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 201 then (LoggedOutMessage.decode bytes).map fun (message, rest) => (.loggedOutMessage message, rest)
  else if tag = 10 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 11 then (TestRequestMessage.decode bytes).map fun (message, rest) => (.testRequestMessage message, rest)
  else if tag = 102 then (ResendRequestMessage.decode bytes).map fun (message, rest) => (.resendRequestMessage message, rest)
  else if tag = 202 then (GapFillMessage.decode bytes).map fun (message, rest) => (.gapFillMessage message, rest)
  else if tag = 210 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  protocolId : BitVec 8
  flags : BitVec 8
  sequenceNumber : BitVec 32
  lastProcessedSeqNo : BitVec 32
  reserved : BitVec 32
  sendTimeEpochNanos : BitVec 64
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  padding : Capped 65431
  deriving DecidableEq, Repr

namespace SbeMessage

def encodeBody (message : SbeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.lastProcessedSeqNo
    ++ (encodeUIntLE 4 message.reserved
    ++ (encodeUIntLE 8 message.sendTimeEpochNanos
    ++ (encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload
    ++ (message.padding.val)))))))))

def decodeBody (protocolId : BitVec 8) (flags : BitVec 8) (bytes : List UInt8) : Option SbeMessage := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (lastProcessedSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (reserved, bytes) ← decodeUIntLE 4 bytes
  let (sendTimeEpochNanos, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65431 then
    pure { protocolId, flags, sequenceNumber, lastProcessedSeqNo, reserved, sendTimeEpochNanos, blockLength, schemaId, version, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : SbeMessage) : decodeBody message.protocolId message.flags (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.padding.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SbeMessage) : (encodeBody message).length + 4 < 256 ^ 2 := by
  have bound_padding := message.padding.length_le
  unfold encodeBody
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logonConfMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonConfMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | loggedOutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LoggedOutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TestRequestMessage.encode_length]
    omega
  | resendRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ResendRequestMessage.encode_length]
    omega
  | gapFillMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, GapFillMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RejectMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 4, so it is written from the body and checked on decode; Protocol Id, Flags are read ahead of it -/
def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 1 message.protocolId
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeFramedLE 2 4 encodeBody message))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (protocolId, bytes) ← decodeUInt 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  decodeFramedAllLE 2 4 (decodeBody protocolId flags) bytes

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFramedAllLE_encodeFramedLE 2 4 encodeBody (decodeBody message.protocolId message.flags) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, encodeUIntLE_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

end SbeMessage

/-- Packet -/
structure Packet where
  sbeMessage : List SbeMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option Packet := do
  let sbeMessage ← decodeAll SbeMessage.decode bytes.length bytes
  pure { sbeMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SbeMessage.encode SbeMessage.decode SbeMessage.decode_encode SbeMessage.encode_length_pos message.sbeMessage _ (encodeMany_length_ge SbeMessage.encode SbeMessage.encode_length_pos message.sbeMessage), some_bind]
  rfl

end Packet

end Omi.CoinbaseCoinbasederivativesSessionTcpV12
