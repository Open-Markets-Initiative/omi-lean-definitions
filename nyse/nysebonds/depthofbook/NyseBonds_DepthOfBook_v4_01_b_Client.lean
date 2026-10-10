import Wire

/-!
# New York Stock Exchange DepthOfBook v4.01.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNysebondsDepthofbookAbpV401BClient

/-- Login Message: 34 bytes -/
structure LoginMessage where
  username : Alpha 8
  password : Alpha 10
  loginSequenceNumber : Alpha 10
  listedSubscription : Alpha 1
  etfSubscription : Alpha 1
  otcSubscription : Alpha 1
  globalOtcSubscription : Alpha 1
  bondSubscription : Alpha 1
  etx : BitVec 8
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.loginSequenceNumber
    ++ (Alpha.encode message.listedSubscription
    ++ (Alpha.encode message.etfSubscription
    ++ (Alpha.encode message.otcSubscription
    ++ (Alpha.encode message.globalOtcSubscription
    ++ (Alpha.encode message.bondSubscription
    ++ (encodeUInt 1 message.etx))))))))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (loginSequenceNumber, bytes) ← Alpha.decode 10 bytes
  let (listedSubscription, bytes) ← Alpha.decode 1 bytes
  let (etfSubscription, bytes) ← Alpha.decode 1 bytes
  let (otcSubscription, bytes) ← Alpha.decode 1 bytes
  let (globalOtcSubscription, bytes) ← Alpha.decode 1 bytes
  let (bondSubscription, bytes) ← Alpha.decode 1 bytes
  let (etx, bytes) ← decodeUInt 1 bytes
  pure ({ username, password, loginSequenceNumber, listedSubscription, etfSubscription, otcSubscription, globalOtcSubscription, bondSubscription, etx }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LoginMessage

/-- Logoff Message: 1 bytes -/
structure LogoffMessage where
  etx : BitVec 8
  deriving DecidableEq, Repr

namespace LogoffMessage

def encode (message : LogoffMessage) : List UInt8 :=
  encodeUInt 1 message.etx

def decode (bytes : List UInt8) : Option (LogoffMessage × List UInt8) := do
  let (etx, bytes) ← decodeUInt 1 bytes
  pure ({ etx }, bytes)

@[simp] theorem encode_length (message : LogoffMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LogoffMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoffMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogoffMessage

/-- Heartbeat Response Message: 1 bytes -/
structure HeartbeatResponseMessage where
  etx : BitVec 8
  deriving DecidableEq, Repr

namespace HeartbeatResponseMessage

def encode (message : HeartbeatResponseMessage) : List UInt8 :=
  encodeUInt 1 message.etx

def decode (bytes : List UInt8) : Option (HeartbeatResponseMessage × List UInt8) := do
  let (etx, bytes) ← decodeUInt 1 bytes
  pure ({ etx }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : HeartbeatResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HeartbeatResponseMessage

/-- Test Request Message: 21 bytes -/
structure TestRequestMessage where
  testRequestText : Alpha 20
  etx : BitVec 8
  deriving DecidableEq, Repr

namespace TestRequestMessage

def encode (message : TestRequestMessage) : List UInt8 :=
  Alpha.encode message.testRequestText
    ++ (encodeUInt 1 message.etx)

def decode (bytes : List UInt8) : Option (TestRequestMessage × List UInt8) := do
  let (testRequestText, bytes) ← Alpha.decode 20 bytes
  let (etx, bytes) ← decodeUInt 1 bytes
  pure ({ testRequestText, etx }, bytes)

@[simp] theorem encode_length (message : TestRequestMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TestRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TestRequestMessage

/-- Any Client Data, selected by Client Message Type -/
inductive ClientData where
  | loginMessage (message : LoginMessage) -- "L" 0x4C
  | logoffMessage (message : LogoffMessage) -- "O" 0x4F
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- "H" 0x48
  | testRequestMessage (message : TestRequestMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace ClientData

/-- The Client Message Type each message is sent under -/
def tag : ClientData → BitVec 8
  | .loginMessage _ => 76
  | .logoffMessage _ => 79
  | .heartbeatResponseMessage _ => 72
  | .testRequestMessage _ => 84

def encode : ClientData → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .logoffMessage message => LogoffMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .testRequestMessage message => TestRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientData) : (encode message).length ≤ 34 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | logoffMessage inner =>
    simp only [encode, LogoffMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [encode, HeartbeatResponseMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [encode, TestRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientData × List UInt8) :=
  if tag = 76 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 79 then (LogoffMessage.decode bytes).map fun (message, rest) => (.logoffMessage message, rest)
  else if tag = 72 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 84 then (TestRequestMessage.decode bytes).map fun (message, rest) => (.testRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientData

/-- Client Packet -/
structure ClientPacket where
  clientData : ClientData
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientData.tag message.clientData)
    ++ (ClientData.encode message.clientData)

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (clientMessageType, bytes) ← decodeUInt 1 bytes
  let (clientData, bytes) ← ClientData.decode clientMessageType bytes
  pure ({ clientData }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientPacket) : (encode message).length ≤ 35 := by
  unfold encode
  cases message.clientData with
  | loginMessage inner =>
    simp only [ClientData.encode, List.length_append, encodeUInt_length, LoginMessage.encode_length]
    omega
  | logoffMessage inner =>
    simp only [ClientData.encode, List.length_append, encodeUInt_length, LogoffMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [ClientData.encode, List.length_append, encodeUInt_length, HeartbeatResponseMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [ClientData.encode, List.length_append, encodeUInt_length, TestRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientData.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.NyseNysebondsDepthofbookAbpV401BClient
