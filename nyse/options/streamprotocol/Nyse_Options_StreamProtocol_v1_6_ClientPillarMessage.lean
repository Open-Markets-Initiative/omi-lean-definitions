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

namespace Omi.NyseOptionsStreamprotocolPillarstreamV16ClientPillarMessage

/-- Login Message -/
structure LoginMessage where
  username : Alpha 16
  password : Alpha 32
  mic : Alpha 4
  version : Alpha 20
  deriving DecidableEq, Repr

namespace LoginMessage

def encodeBody (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.version)))

def decodeBody (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (version, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, mic, version }, bytes)

theorem decodeBody_encodeBody (message : LoginMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : LoginMessage) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : LoginMessage → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (LoginMessage × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end LoginMessage

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

/-- Open -/
structure Open where
  streamId : StreamId
  startSeq : BitVec 64
  endSeq : BitVec 64
  access : BitVec 8
  mode : BitVec 8
  deriving DecidableEq, Repr

namespace Open

def encodeBody (message : Open) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.startSeq
    ++ (encodeUIntLE 8 message.endSeq
    ++ (encodeUInt 1 message.access
    ++ (encodeUInt 1 message.mode))))

def decodeBody (bytes : List UInt8) : Option (Open × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (startSeq, bytes) ← decodeUIntLE 8 bytes
  let (endSeq, bytes) ← decodeUIntLE 8 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  let (mode, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, startSeq, endSeq, access, mode }, bytes)

theorem decodeBody_encodeBody (message : Open) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Open) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUIntLE_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Open → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Open × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Open) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Open) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Open

/-- Close -/
structure Close where
  streamId : StreamId
  deriving DecidableEq, Repr

namespace Close

def encodeBody (message : Close) : List UInt8 :=
  StreamId.encode message.streamId

def decodeBody (bytes : List UInt8) : Option (Close × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  pure ({ streamId }, bytes)

theorem decodeBody_encodeBody (message : Close) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [StreamId.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Close) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [StreamId.encode_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Close → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Close × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Close) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Close) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Close

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

/-- Client Seq Msg -/
structure ClientSeqMsg where
  seqMsgId : SeqMsgId
  reserved4 : BitVec 32
  timestamp : BitVec 64
  seqMsgType : BitVec 16
  clientSequencedMessage : Counting 2 4 UInt8
  deriving DecidableEq, Repr

namespace ClientSeqMsg

def encodeBody (message : ClientSeqMsg) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (encodeUIntLE 4 message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.seqMsgType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) (message.clientSequencedMessage.val.length + 4))
    ++ (encodeMany Byte.encode message.clientSequencedMessage.val)))))

def decodeBody (bytes : List UInt8) : Option (ClientSeqMsg × List UInt8) := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let (clientSequencedMessage_, bytes) ← decodeMany Byte.decode (seqMsgLength.toNat - 4) bytes
  if fits_clientSequencedMessage : clientSequencedMessage_.length + 4 < 256 ^ 2 then
    pure ({ seqMsgId, reserved4, timestamp, seqMsgType, clientSequencedMessage := ⟨clientSequencedMessage_, fits_clientSequencedMessage⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : ClientSeqMsg) (rest : List UInt8) :
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
  rw [dite_eq_left message.clientSequencedMessage.length_lt]
  rfl

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientSeqMsg) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 4)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientSeqMsg × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientSeqMsg) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ClientSeqMsg

/-- Any Client Message, selected by Msg Type -/
inductive ClientMessage where
  | loginMessage (message : LoginMessage) -- 513
  | heartbeat (message : Heartbeat) -- 516
  | open_ (message : Open) -- 517
  | close (message : Close) -- 519
  | clientSeqMsg (message : ClientSeqMsg) -- 2309
  deriving DecidableEq, Repr

namespace ClientMessage

/-- The Msg Type each message is sent under -/
def tag : ClientMessage → BitVec 16
  | .loginMessage _ => 513
  | .heartbeat _ => 516
  | .open_ _ => 517
  | .close _ => 519
  | .clientSeqMsg _ => 2309

def encode : ClientMessage → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .open_ message => Open.encode message
  | .close message => Close.encode message
  | .clientSeqMsg message => ClientSeqMsg.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessage × List UInt8) :=
  if tag = 513 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 516 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 517 then (Open.decode bytes).map fun (message, rest) => (.open_ message, rest)
  else if tag = 519 then (Close.decode bytes).map fun (message, rest) => (.close message, rest)
  else if tag = 2309 then (ClientSeqMsg.decode bytes).map fun (message, rest) => (.clientSeqMsg message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessage

/-- Client Pillar Message -/
structure ClientPillarMessage where
  clientMessage : ClientMessage
  deriving DecidableEq, Repr

namespace ClientPillarMessage

def encode (message : ClientPillarMessage) : List UInt8 :=
  encodeUIntLE 2 (ClientMessage.tag message.clientMessage)
    ++ (ClientMessage.encode message.clientMessage)

def decode (bytes : List UInt8) : Option (ClientPillarMessage × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (clientMessage, bytes) ← ClientMessage.decode msgType bytes
  pure ({ clientMessage }, bytes)

theorem encode_length_pos (message : ClientPillarMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ClientPillarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientMessage.decode_encode, some_bind]
  rfl

end ClientPillarMessage

end Omi.NyseOptionsStreamprotocolPillarstreamV16ClientPillarMessage
