import Omi.Wire

/-!
# TMX Group Sola Multicast v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolamulticastHsvfV21

/-- Login Message: 40 bytes -/
structure LoginMessage where
  user : Alpha 16
  pwd : Alpha 16
  timestamp : Alpha 6
  protocol : Alpha 2
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.user
    ++ (Alpha.encode message.pwd
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.protocol)))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (user, bytes) ← Alpha.decode 16 bytes
  let (pwd, bytes) ← Alpha.decode 16 bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (protocol, bytes) ← Alpha.decode 2 bytes
  pure ({ user, pwd, timestamp, protocol }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
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

end LoginMessage

/-- Retransmission Request Message: 20 bytes -/
structure RetransmissionRequestMessage where
  line : Alpha 2
  start : Alpha 9
  end_ : Alpha 9
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  Alpha.encode message.line
    ++ (Alpha.encode message.start
    ++ (Alpha.encode message.end_))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (line, bytes) ← Alpha.decode 2 bytes
  let (start, bytes) ← Alpha.decode 9 bytes
  let (end_, bytes) ← Alpha.decode 9 bytes
  pure ({ line, start, end_ }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Error Message: 84 bytes -/
structure ErrorMessage where
  errorCode : Alpha 4
  errorMsg : Alpha 80
  deriving DecidableEq, Repr

namespace ErrorMessage

def encode (message : ErrorMessage) : List UInt8 :=
  Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorMsg)

def decode (bytes : List UInt8) : Option (ErrorMessage × List UInt8) := do
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorMsg, bytes) ← Alpha.decode 80 bytes
  pure ({ errorCode, errorMsg }, bytes)

@[simp] theorem encode_length (message : ErrorMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | loginMessage (message : LoginMessage) -- "LI" 0x4C49
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- "RT" 0x5254
  | errorMessage (message : ErrorMessage) -- "ER" 0x4552
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .loginMessage _ => 19529
  | .retransmissionRequestMessage _ => 21076
  | .errorMessage _ => 17746

def encode : MessageBody → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .errorMessage message => ErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 84 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | errorMessage inner =>
    simp only [encode, ErrorMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 19529 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 21076 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 17746 then (ErrorMessage.decode bytes).map fun (message, rest) => (.errorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  hsvfStx : BitVec 8
  sequenceNumber : Alpha 9
  messageBody : MessageBody
  hsvfEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.hsvfStx
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.hsvfEtx))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (hsvfStx, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (hsvfEtx, bytes) ← decodeUInt 1 bytes
  pure ({ hsvfStx, sequenceNumber, messageBody, hsvfEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 97 := by
  unfold encode
  cases message.messageBody with
  | loginMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionRequestMessage.encode_length]
    omega
  | errorMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxMxSolamulticastHsvfV21
