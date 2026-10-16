import Wire

/-!
# New York Stock Exchange Stream Protocol v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseOptionsStreamprotocolPillarstreamV16ServerPillarMessage

/-- Login Response -/
structure LoginResponse where
  username : Alpha 16
  status : BitVec 8
  deriving DecidableEq, Repr

namespace LoginResponse

def encodeBody (message : LoginResponse) : List UInt8 :=
  Alpha.encode message.username
    ++ (encodeUInt 1 message.status)

def decodeBody (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  pure ({ username, status }, bytes)

theorem decodeBody_encodeBody (message : LoginResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : LoginResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : LoginResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (LoginResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end LoginResponse

/-- Stream Id: 8 bytes -/
structure StreamId where
  sess : BitVec 32
  user : BitVec 32
  deriving DecidableEq, Repr

namespace StreamId

def encode (message : StreamId) : List UInt8 :=
  encodeUIntLE 4 message.sess
    ++ (encodeUIntLE 4 message.user)

def decode (bytes : List UInt8) : Option (StreamId × List UInt8) := do
  let (sess, bytes) ← decodeUIntLE 4 bytes
  let (user, bytes) ← decodeUIntLE 4 bytes
  pure ({ sess, user }, bytes)

@[simp] theorem encode_length (message : StreamId) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StreamId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StreamId

/-- Stream Avail -/
structure StreamAvail where
  streamId : StreamId
  nextSeq : BitVec 64
  access : BitVec 8
  deriving DecidableEq, Repr

namespace StreamAvail

def encodeBody (message : StreamAvail) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.nextSeq
    ++ (encodeUInt 1 message.access))

def decodeBody (bytes : List UInt8) : Option (StreamAvail × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (nextSeq, bytes) ← decodeUIntLE 8 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, nextSeq, access }, bytes)

theorem decodeBody_encodeBody (message : StreamAvail) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : StreamAvail) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUIntLE_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : StreamAvail → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (StreamAvail × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : StreamAvail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : StreamAvail) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end StreamAvail

/-- Heartbeat -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encodeBody (_ : Heartbeat) : List UInt8 :=
  []

def decodeBody (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

theorem decodeBody_encodeBody (message : Heartbeat) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Heartbeat) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_nil]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Heartbeat → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Heartbeat × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Heartbeat

/-- Open Response -/
structure OpenResponse where
  streamId : StreamId
  status : BitVec 8
  access : BitVec 8
  deriving DecidableEq, Repr

namespace OpenResponse

def encodeBody (message : OpenResponse) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.access))

def decodeBody (bytes : List UInt8) : Option (OpenResponse × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, status, access }, bytes)

theorem decodeBody_encodeBody (message : OpenResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OpenResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : OpenResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (OpenResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : OpenResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OpenResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end OpenResponse

/-- Close Response -/
structure CloseResponse where
  streamId : StreamId
  status : BitVec 8
  deriving DecidableEq, Repr

namespace CloseResponse

def encodeBody (message : CloseResponse) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUInt 1 message.status)

def decodeBody (bytes : List UInt8) : Option (CloseResponse × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (status, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, status }, bytes)

theorem decodeBody_encodeBody (message : CloseResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CloseResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, StreamId.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : CloseResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (CloseResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : CloseResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CloseResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end CloseResponse

/-- Seq Msg Id: 16 bytes -/
structure SeqMsgId where
  streamId : StreamId
  seq : BitVec 64
  deriving DecidableEq, Repr

namespace SeqMsgId

def encode (message : SeqMsgId) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.seq)

def decode (bytes : List UInt8) : Option (SeqMsgId × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (seq, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamId, seq }, bytes)

@[simp] theorem encode_length (message : SeqMsgId) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, StreamId.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SeqMsgId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeqMsgId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SeqMsgId

/-- Server Seq Msg -/
structure ServerSeqMsg where
  seqMsgId : SeqMsgId
  reserved4 : BitVec 32
  timestamp : BitVec 64
  seqMsgType : BitVec 16
  serverSequencedMessage : Counting 2 4 UInt8
  deriving DecidableEq, Repr

namespace ServerSeqMsg

def encodeBody (message : ServerSeqMsg) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (encodeUIntLE 4 message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.seqMsgType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) (message.serverSequencedMessage.val.length + 4))
    ++ (encodeMany Byte.encode message.serverSequencedMessage.val)))))

def decodeBody (bytes : List UInt8) : Option (ServerSeqMsg × List UInt8) := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let (serverSequencedMessage_, bytes) ← decodeMany Byte.decode (seqMsgLength.toNat - 4) bytes
  if fits_serverSequencedMessage : serverSequencedMessage_.length + 4 < 256 ^ 2 then
    pure ({ seqMsgId, reserved4, timestamp, seqMsgType, serverSequencedMessage := ⟨serverSequencedMessage_, fits_serverSequencedMessage⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : ServerSeqMsg) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, SeqMsgId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_counting 2 4 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.serverSequencedMessage.length_lt]
  rfl

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ServerSeqMsg) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 4)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ServerSeqMsg × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ServerSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ServerSeqMsg) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ServerSeqMsg

/-- Any Server Message, selected by Msg Type -/
inductive ServerMessage where
  | loginResponse (message : LoginResponse) -- 514
  | streamAvail (message : StreamAvail) -- 515
  | heartbeat (message : Heartbeat) -- 516
  | openResponse (message : OpenResponse) -- 518
  | closeResponse (message : CloseResponse) -- 520
  | serverSeqMsg (message : ServerSeqMsg) -- 2309
  deriving DecidableEq, Repr

namespace ServerMessage

/-- The Msg Type each message is sent under -/
def tag : ServerMessage → BitVec 16
  | .loginResponse _ => 514
  | .streamAvail _ => 515
  | .heartbeat _ => 516
  | .openResponse _ => 518
  | .closeResponse _ => 520
  | .serverSeqMsg _ => 2309

def encode : ServerMessage → List UInt8
  | .loginResponse message => LoginResponse.encode message
  | .streamAvail message => StreamAvail.encode message
  | .heartbeat message => Heartbeat.encode message
  | .openResponse message => OpenResponse.encode message
  | .closeResponse message => CloseResponse.encode message
  | .serverSeqMsg message => ServerSeqMsg.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessage × List UInt8) :=
  if tag = 514 then (LoginResponse.decode bytes).map fun (message, rest) => (.loginResponse message, rest)
  else if tag = 515 then (StreamAvail.decode bytes).map fun (message, rest) => (.streamAvail message, rest)
  else if tag = 516 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 518 then (OpenResponse.decode bytes).map fun (message, rest) => (.openResponse message, rest)
  else if tag = 520 then (CloseResponse.decode bytes).map fun (message, rest) => (.closeResponse message, rest)
  else if tag = 2309 then (ServerSeqMsg.decode bytes).map fun (message, rest) => (.serverSeqMsg message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessage

/-- Server Pillar Message -/
structure ServerPillarMessage where
  serverMessage : ServerMessage
  deriving DecidableEq, Repr

namespace ServerPillarMessage

def encode (message : ServerPillarMessage) : List UInt8 :=
  encodeUIntLE 2 (ServerMessage.tag message.serverMessage)
    ++ (ServerMessage.encode message.serverMessage)

def decode (bytes : List UInt8) : Option (ServerPillarMessage × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (serverMessage, bytes) ← ServerMessage.decode msgType bytes
  pure ({ serverMessage }, bytes)

theorem encode_length_pos (message : ServerPillarMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ServerPillarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ServerMessage.decode_encode, some_bind]
  rfl

end ServerPillarMessage

end Omi.NyseOptionsStreamprotocolPillarstreamV16ServerPillarMessage
