import Wire

/-!
# New York Stock Exchange Binary Gateway v3.25

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseAmexoptionsBinarygatewayPillarstreamV325ClientPillarMessage

/-- Risk User Type: one byte code -/
def RiskUserType.codes : List UInt8 :=
  [0x45, 0x43, 0x4F]

inductive RiskUserType where
  | enteringFirm -- Entering Firm
  | clearingFirm -- Clearing Firm
  | optionsMarketMakerFirm -- Options Market Maker Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ RiskUserType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RiskUserType

def toByte : RiskUserType → UInt8
  | .enteringFirm => 0x45
  | .clearingFirm => 0x43
  | .optionsMarketMakerFirm => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RiskUserType :=
  if byte = 0x45 then .enteringFirm
  else if byte = 0x43 then .clearingFirm
  else .optionsMarketMakerFirm

def ofByte (byte : UInt8) : RiskUserType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RiskUserType) : ofByte value.toByte = value := by
  cases value with
  | enteringFirm => decide
  | clearingFirm => decide
  | optionsMarketMakerFirm => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RiskUserType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RiskUserType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RiskUserType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RiskUserType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RiskUserType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RiskUserType

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

/-- Session Configuration Request Message: 70 bytes -/
structure SessionConfigurationRequestMessage where
  username : Alpha 16
  cancelOnDisconnect : BitVec 8
  throttlePreference : BitVec 8
  selfTradePrevention : BitVec 8
  orderPriorityUpdateAckSubscription : BitVec 8
  boldDesignation : BitVec 8
  reserved49 : Alpha 49
  deriving DecidableEq, Repr

namespace SessionConfigurationRequestMessage

def encode (message : SessionConfigurationRequestMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (encodeUIntLE 1 message.cancelOnDisconnect
    ++ (encodeUIntLE 1 message.throttlePreference
    ++ (encodeUIntLE 1 message.selfTradePrevention
    ++ (encodeUIntLE 1 message.orderPriorityUpdateAckSubscription
    ++ (encodeUIntLE 1 message.boldDesignation
    ++ (Alpha.encode message.reserved49))))))

def decode (bytes : List UInt8) : Option (SessionConfigurationRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (cancelOnDisconnect, bytes) ← decodeUIntLE 1 bytes
  let (throttlePreference, bytes) ← decodeUIntLE 1 bytes
  let (selfTradePrevention, bytes) ← decodeUIntLE 1 bytes
  let (orderPriorityUpdateAckSubscription, bytes) ← decodeUIntLE 1 bytes
  let (boldDesignation, bytes) ← decodeUIntLE 1 bytes
  let (reserved49, bytes) ← Alpha.decode 49 bytes
  pure ({ username, cancelOnDisconnect, throttlePreference, selfTradePrevention, orderPriorityUpdateAckSubscription, boldDesignation, reserved49 }, bytes)

@[simp] theorem encode_length (message : SessionConfigurationRequestMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SessionConfigurationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionConfigurationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SessionConfigurationRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionConfigurationRequestMessage

/-- Sequenced Filler Message: 0 bytes -/
structure SequencedFillerMessage where
  deriving DecidableEq, Repr

namespace SequencedFillerMessage

def encode (_ : SequencedFillerMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SequencedFillerMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SequencedFillerMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SequencedFillerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedFillerMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedFillerMessage

/-- Sub Msg Header: 4 bytes -/
structure SubMsgHeader where
  subMsgType : BitVec 16
  subMsgLength : BitVec 16
  deriving DecidableEq, Repr

namespace SubMsgHeader

def encode (message : SubMsgHeader) : List UInt8 :=
  encodeUIntLE 2 message.subMsgType
    ++ (encodeUIntLE 2 message.subMsgLength)

def decode (bytes : List UInt8) : Option (SubMsgHeader × List UInt8) := do
  let (subMsgType, bytes) ← decodeUIntLE 2 bytes
  let (subMsgLength, bytes) ← decodeUIntLE 2 bytes
  pure ({ subMsgType, subMsgLength }, bytes)

@[simp] theorem encode_length (message : SubMsgHeader) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SubMsgHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubMsgHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SubMsgHeader

/-- Optional Order Add On: 47 bytes -/
structure OptionalOrderAddOn where
  subMsgHeader : SubMsgHeader
  stopPx : BitVec 64
  maxFloor : BitVec 32
  deliverToCompId : Alpha 5
  clearingFirm : Alpha 5
  optionalData : Alpha 16
  clearingAccount : Alpha 5
  deriving DecidableEq, Repr

namespace OptionalOrderAddOn

def encode (message : OptionalOrderAddOn) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 4 message.maxFloor
    ++ (Alpha.encode message.deliverToCompId
    ++ (Alpha.encode message.clearingFirm
    ++ (Alpha.encode message.optionalData
    ++ (Alpha.encode message.clearingAccount))))))

def decode (bytes : List UInt8) : Option (OptionalOrderAddOn × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 4 bytes
  let (deliverToCompId, bytes) ← Alpha.decode 5 bytes
  let (clearingFirm, bytes) ← Alpha.decode 5 bytes
  let (optionalData, bytes) ← Alpha.decode 16 bytes
  let (clearingAccount, bytes) ← Alpha.decode 5 bytes
  pure ({ subMsgHeader, stopPx, maxFloor, deliverToCompId, clearingFirm, optionalData, clearingAccount }, bytes)

@[simp] theorem encode_length (message : OptionalOrderAddOn) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionalOrderAddOn) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionalOrderAddOn) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionalOrderAddOn

/-- New Order Message -/
structure NewOrderMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  bitfieldOrderInstructions : Alpha 16
  price : BitVec 64
  orderQty : BitVec 32
  minQty : BitVec 32
  userData : Alpha 10
  legOpenClose : BitVec 64
  auctionId : BitVec 64
  optionalOrderAddOn : Option OptionalOrderAddOn
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (Alpha.encode message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 8 message.legOpenClose
    ++ (encodeUIntLE 8 message.auctionId
    ++ (encodeOptional (OptionalOrderAddOn.encode) message.optionalOrderAddOn)))))))))))))

def decode (bytes : List UInt8) : Option NewOrderMessage := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldOrderInstructions, bytes) ← Alpha.decode 16 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (legOpenClose, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let optionalOrderAddOn ← decodeRemaining (OptionalOrderAddOn.decode) bytes
  pure { symbolId, mpid, marketMaker, mpSubId, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, userData, legOpenClose, auctionId, optionalOrderAddOn }

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : NewOrderMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeRemaining_encodeOptional (OptionalOrderAddOn.encode) (OptionalOrderAddOn.decode) (OptionalOrderAddOn.decode_encode) (OptionalOrderAddOn.encode_length_pos), some_bind]
  rfl

end NewOrderMessage

/-- Order Cancel Request Message: 24 bytes -/
structure OrderCancelRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId)))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, mpid, clOrdId, origClOrdId }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderCancelRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderCancelRequestMessage

/-- Order Modify Request Message: 30 bytes -/
structure OrderModifyRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  orderQty : BitVec 32
  sideU81 : BitVec 8
  locateReqdU81 : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyRequestMessage

def encode (message : OrderModifyRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.sideU81
    ++ (encodeUIntLE 1 message.locateReqdU81))))))

def decode (bytes : List UInt8) : Option (OrderModifyRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (sideU81, bytes) ← decodeUIntLE 1 bytes
  let (locateReqdU81, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolId, mpid, clOrdId, origClOrdId, orderQty, sideU81, locateReqdU81 }, bytes)

@[simp] theorem encode_length (message : OrderModifyRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModifyRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderModifyRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderModifyRequestMessage

/-- Quote Request Group: 17 bytes -/
structure QuoteRequestGroup where
  seriesIndex : BitVec 32
  bitfieldQuoteInst : BitVec 8
  price : BitVec 64
  orderQty : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteRequestGroup

def encode (message : QuoteRequestGroup) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.bitfieldQuoteInst
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty)))

def decode (bytes : List UInt8) : Option (QuoteRequestGroup × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (bitfieldQuoteInst, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ seriesIndex, bitfieldQuoteInst, price, orderQty }, bytes)

@[simp] theorem encode_length (message : QuoteRequestGroup) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteRequestGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteRequestGroup

/-- New Bulk Quote Type 243 Message -/
structure NewBulkQuoteType243Message where
  mpid : Alpha 4
  marketMaker : Alpha 10
  subId : Alpha 4
  clOrdId : BitVec 64
  selfTradeTypeU81 : BitVec 8
  groupId : BitVec 32
  mmSentTime : BitVec 64
  quoteRequestGroup : List QuoteRequestGroup
  deriving DecidableEq, Repr

namespace NewBulkQuoteType243Message

def encode (message : NewBulkQuoteType243Message) : List UInt8 :=
  Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.subId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.selfTradeTypeU81
    ++ (encodeUIntLE 4 message.groupId
    ++ (encodeUIntLE 8 message.mmSentTime
    ++ (encodeMany QuoteRequestGroup.encode message.quoteRequestGroup)))))))

def decode (bytes : List UInt8) : Option NewBulkQuoteType243Message := do
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (subId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (selfTradeTypeU81, bytes) ← decodeUIntLE 1 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (mmSentTime, bytes) ← decodeUIntLE 8 bytes
  let quoteRequestGroup ← decodeAll QuoteRequestGroup.decode bytes.length bytes
  pure { mpid, marketMaker, subId, clOrdId, selfTradeTypeU81, groupId, mmSentTime, quoteRequestGroup }

theorem encode_length_pos (message : NewBulkQuoteType243Message) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : NewBulkQuoteType243Message) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeAll_encodeMany QuoteRequestGroup.encode QuoteRequestGroup.decode QuoteRequestGroup.decode_encode QuoteRequestGroup.encode_length_pos message.quoteRequestGroup _ (encodeMany_length_ge QuoteRequestGroup.encode QuoteRequestGroup.encode_length_pos message.quoteRequestGroup), some_bind]
  rfl

end NewBulkQuoteType243Message

/-- New Bulk Quote Type 259 Message -/
structure NewBulkQuoteType259Message where
  mpid : Alpha 4
  marketMaker : Alpha 10
  subId : Alpha 4
  clOrdId : BitVec 64
  selfTradeTypeU81 : BitVec 8
  groupId : BitVec 32
  mmSentTime : BitVec 64
  quoteRequestGroup : List QuoteRequestGroup
  deriving DecidableEq, Repr

namespace NewBulkQuoteType259Message

def encode (message : NewBulkQuoteType259Message) : List UInt8 :=
  Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.subId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.selfTradeTypeU81
    ++ (encodeUIntLE 4 message.groupId
    ++ (encodeUIntLE 8 message.mmSentTime
    ++ (encodeMany QuoteRequestGroup.encode message.quoteRequestGroup)))))))

def decode (bytes : List UInt8) : Option NewBulkQuoteType259Message := do
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (subId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (selfTradeTypeU81, bytes) ← decodeUIntLE 1 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (mmSentTime, bytes) ← decodeUIntLE 8 bytes
  let quoteRequestGroup ← decodeAll QuoteRequestGroup.decode bytes.length bytes
  pure { mpid, marketMaker, subId, clOrdId, selfTradeTypeU81, groupId, mmSentTime, quoteRequestGroup }

theorem encode_length_pos (message : NewBulkQuoteType259Message) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : NewBulkQuoteType259Message) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeAll_encodeMany QuoteRequestGroup.encode QuoteRequestGroup.decode QuoteRequestGroup.decode_encode QuoteRequestGroup.encode_length_pos message.quoteRequestGroup _ (encodeMany_length_ge QuoteRequestGroup.encode QuoteRequestGroup.encode_length_pos message.quoteRequestGroup), some_bind]
  rfl

end NewBulkQuoteType259Message

/-- Exposed: 147 bytes -/
structure Exposed where
  subMsgHeader : SubMsgHeader
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  bitfieldOrderInstructions : Alpha 16
  price : BitVec 64
  orderQty : BitVec 32
  minQty : BitVec 32
  userData : Alpha 10
  legOpenClose : BitVec 64
  auctionId : BitVec 64
  optionalOrderAddOn : OptionalOrderAddOn
  deriving DecidableEq, Repr

namespace Exposed

def encode (message : Exposed) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (Alpha.encode message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 8 message.legOpenClose
    ++ (encodeUIntLE 8 message.auctionId
    ++ (OptionalOrderAddOn.encode message.optionalOrderAddOn))))))))))))))

def decode (bytes : List UInt8) : Option (Exposed × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldOrderInstructions, bytes) ← Alpha.decode 16 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (legOpenClose, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (optionalOrderAddOn, bytes) ← OptionalOrderAddOn.decode bytes
  pure ({ subMsgHeader, symbolId, mpid, marketMaker, mpSubId, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, userData, legOpenClose, auctionId, optionalOrderAddOn }, bytes)

@[simp] theorem encode_length (message : Exposed) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, encodeUIntLE_length, Alpha.encode_length, OptionalOrderAddOn.encode_length]

theorem encode_length_pos (message : Exposed) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Exposed) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OptionalOrderAddOn.decode_encode, some_bind]
  rfl

end Exposed

/-- Covered: 147 bytes -/
structure Covered where
  subMsgHeader : SubMsgHeader
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  bitfieldOrderInstructions : Alpha 16
  price : BitVec 64
  orderQty : BitVec 32
  minQty : BitVec 32
  userData : Alpha 10
  legOpenClose : BitVec 64
  auctionId : BitVec 64
  optionalOrderAddOn : OptionalOrderAddOn
  deriving DecidableEq, Repr

namespace Covered

def encode (message : Covered) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (Alpha.encode message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 8 message.legOpenClose
    ++ (encodeUIntLE 8 message.auctionId
    ++ (OptionalOrderAddOn.encode message.optionalOrderAddOn))))))))))))))

def decode (bytes : List UInt8) : Option (Covered × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldOrderInstructions, bytes) ← Alpha.decode 16 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (legOpenClose, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (optionalOrderAddOn, bytes) ← OptionalOrderAddOn.decode bytes
  pure ({ subMsgHeader, symbolId, mpid, marketMaker, mpSubId, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, userData, legOpenClose, auctionId, optionalOrderAddOn }, bytes)

@[simp] theorem encode_length (message : Covered) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, encodeUIntLE_length, Alpha.encode_length, OptionalOrderAddOn.encode_length]

theorem encode_length_pos (message : Covered) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Covered) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OptionalOrderAddOn.decode_encode, some_bind]
  rfl

end Covered

/-- New Order Cross Message: 371 bytes -/
structure NewOrderCrossMessage where
  crossId : BitVec 64
  allocationPct : BitVec 8
  clearingFirmExposed : Alpha 5
  clearingAccountExposed : Alpha 5
  optionalDataExposed : Alpha 16
  clearingFirmCovered : Alpha 5
  clearingAccountCovered : Alpha 5
  optionalDataCovered : Alpha 16
  reserved16 : Alpha 16
  exposed : Exposed
  covered : Covered
  deriving DecidableEq, Repr

namespace NewOrderCrossMessage

def encode (message : NewOrderCrossMessage) : List UInt8 :=
  encodeUIntLE 8 message.crossId
    ++ (encodeUIntLE 1 message.allocationPct
    ++ (Alpha.encode message.clearingFirmExposed
    ++ (Alpha.encode message.clearingAccountExposed
    ++ (Alpha.encode message.optionalDataExposed
    ++ (Alpha.encode message.clearingFirmCovered
    ++ (Alpha.encode message.clearingAccountCovered
    ++ (Alpha.encode message.optionalDataCovered
    ++ (Alpha.encode message.reserved16
    ++ (Exposed.encode message.exposed
    ++ (Covered.encode message.covered))))))))))

def decode (bytes : List UInt8) : Option (NewOrderCrossMessage × List UInt8) := do
  let (crossId, bytes) ← decodeUIntLE 8 bytes
  let (allocationPct, bytes) ← decodeUIntLE 1 bytes
  let (clearingFirmExposed, bytes) ← Alpha.decode 5 bytes
  let (clearingAccountExposed, bytes) ← Alpha.decode 5 bytes
  let (optionalDataExposed, bytes) ← Alpha.decode 16 bytes
  let (clearingFirmCovered, bytes) ← Alpha.decode 5 bytes
  let (clearingAccountCovered, bytes) ← Alpha.decode 5 bytes
  let (optionalDataCovered, bytes) ← Alpha.decode 16 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (exposed, bytes) ← Exposed.decode bytes
  let (covered, bytes) ← Covered.decode bytes
  pure ({ crossId, allocationPct, clearingFirmExposed, clearingAccountExposed, optionalDataExposed, clearingFirmCovered, clearingAccountCovered, optionalDataCovered, reserved16, exposed, covered }, bytes)

@[simp] theorem encode_length (message : NewOrderCrossMessage) : (encode message).length = 371 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Exposed.encode_length, Covered.encode_length]

theorem encode_length_pos (message : NewOrderCrossMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderCrossMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Exposed.decode_encode, some_bind]
  dsimp only
  rw [Covered.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderCrossMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NewOrderCrossMessage

/-- Bulk Cancel Request Type 223 Message: 61 bytes -/
structure BulkCancelRequestType223Message where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  clOrdId : BitVec 64
  mmSentTime : BitVec 64
  sideU81 : BitVec 8
  groupId : BitVec 32
  targetCancelUsername : Alpha 16
  bulkAction : BitVec 8
  cancelScope : BitVec 8
  targetCancelMpid : Alpha 4
  deriving DecidableEq, Repr

namespace BulkCancelRequestType223Message

def encode (message : BulkCancelRequestType223Message) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.mmSentTime
    ++ (encodeUIntLE 1 message.sideU81
    ++ (encodeUIntLE 4 message.groupId
    ++ (Alpha.encode message.targetCancelUsername
    ++ (encodeUIntLE 1 message.bulkAction
    ++ (encodeUIntLE 1 message.cancelScope
    ++ (Alpha.encode message.targetCancelMpid))))))))))

def decode (bytes : List UInt8) : Option (BulkCancelRequestType223Message × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (mmSentTime, bytes) ← decodeUIntLE 8 bytes
  let (sideU81, bytes) ← decodeUIntLE 1 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (targetCancelUsername, bytes) ← Alpha.decode 16 bytes
  let (bulkAction, bytes) ← decodeUIntLE 1 bytes
  let (cancelScope, bytes) ← decodeUIntLE 1 bytes
  let (targetCancelMpid, bytes) ← Alpha.decode 4 bytes
  pure ({ symbolId, mpid, marketMaker, clOrdId, mmSentTime, sideU81, groupId, targetCancelUsername, bulkAction, cancelScope, targetCancelMpid }, bytes)

@[simp] theorem encode_length (message : BulkCancelRequestType223Message) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkCancelRequestType223Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkCancelRequestType223Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BulkCancelRequestType223Message) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BulkCancelRequestType223Message

/-- Bulk Cancel Request Type 224 Message: 62 bytes -/
structure BulkCancelRequestType224Message where
  symbolId : BitVec 32
  mpid : Alpha 4
  mpSubId : Alpha 4
  clOrdId : BitVec 64
  sideU81 : BitVec 8
  targetCancelUsername : Alpha 16
  bulkAction : BitVec 8
  targetCancelMpid : Alpha 4
  reserved20 : Alpha 20
  deriving DecidableEq, Repr

namespace BulkCancelRequestType224Message

def encode (message : BulkCancelRequestType224Message) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.mpSubId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.sideU81
    ++ (Alpha.encode message.targetCancelUsername
    ++ (encodeUIntLE 1 message.bulkAction
    ++ (Alpha.encode message.targetCancelMpid
    ++ (Alpha.encode message.reserved20))))))))

def decode (bytes : List UInt8) : Option (BulkCancelRequestType224Message × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (sideU81, bytes) ← decodeUIntLE 1 bytes
  let (targetCancelUsername, bytes) ← Alpha.decode 16 bytes
  let (bulkAction, bytes) ← decodeUIntLE 1 bytes
  let (targetCancelMpid, bytes) ← Alpha.decode 4 bytes
  let (reserved20, bytes) ← Alpha.decode 20 bytes
  pure ({ symbolId, mpid, mpSubId, clOrdId, sideU81, targetCancelUsername, bulkAction, targetCancelMpid, reserved20 }, bytes)

@[simp] theorem encode_length (message : BulkCancelRequestType224Message) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkCancelRequestType224Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkCancelRequestType224Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BulkCancelRequestType224Message) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BulkCancelRequestType224Message

/-- Risk Limit Update Request Message: 268 bytes -/
structure RiskLimitUpdateRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskControlActivation : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionRequest : BitVec 8
  iocAttribution : BitVec 8
  riskRangeId : BitVec 8
  riskMinimumValue : BitVec 64
  priceScale : BitVec 8
  reserved190 : Alpha 190
  deriving DecidableEq, Repr

namespace RiskLimitUpdateRequestMessage

def encode (message : RiskLimitUpdateRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskControlActivation
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionRequest
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (encodeUIntLE 8 message.riskMinimumValue
    ++ (encodeUIntLE 1 message.priceScale
    ++ (Alpha.encode message.reserved190))))))))))))))))))))

def decode (bytes : List UInt8) : Option (RiskLimitUpdateRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskControlActivation, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionRequest, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (riskMinimumValue, bytes) ← decodeUIntLE 8 bytes
  let (priceScale, bytes) ← decodeUIntLE 1 bytes
  let (reserved190, bytes) ← Alpha.decode 190 bytes
  pure ({ symbolId, mpid, marketMaker, mpSubId, reserved4, clearingNumber, clOrdId, riskUserCrd, riskUserType, riskControlType, riskControlActivation, usdLimit, timeLimit, percentageLimit, countLimit, breachActionRequest, iocAttribution, riskRangeId, riskMinimumValue, priceScale, reserved190 }, bytes)

@[simp] theorem encode_length (message : RiskLimitUpdateRequestMessage) : (encode message).length = 268 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskLimitUpdateRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitUpdateRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RiskUserType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskLimitUpdateRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskLimitUpdateRequestMessage

/-- Risk Action Request Message: 246 bytes -/
structure RiskActionRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskActionType : BitVec 8
  riskRangeId : BitVec 8
  reserved199 : Alpha 199
  deriving DecidableEq, Repr

namespace RiskActionRequestMessage

def encode (message : RiskActionRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (Alpha.encode message.reserved199))))))))))))

def decode (bytes : List UInt8) : Option (RiskActionRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (reserved199, bytes) ← Alpha.decode 199 bytes
  pure ({ symbolId, mpid, marketMaker, mpSubId, reserved4, clearingNumber, clOrdId, riskUserCrd, riskUserType, riskControlType, riskActionType, riskRangeId, reserved199 }, bytes)

@[simp] theorem encode_length (message : RiskActionRequestMessage) : (encode message).length = 246 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskActionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskActionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RiskUserType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskActionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskActionRequestMessage

/-- Complex Series Leg Group: 7 bytes -/
structure ComplexSeriesLegGroup where
  legSymbolId : BitVec 32
  legRatioQty : BitVec 16
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace ComplexSeriesLegGroup

def encode (message : ComplexSeriesLegGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSymbolId
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (encodeUIntLE 1 message.legSide))

def decode (bytes : List UInt8) : Option (ComplexSeriesLegGroup × List UInt8) := do
  let (legSymbolId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← decodeUIntLE 1 bytes
  pure ({ legSymbolId, legRatioQty, legSide }, bytes)

@[simp] theorem encode_length (message : ComplexSeriesLegGroup) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ComplexSeriesLegGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexSeriesLegGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ComplexSeriesLegGroup

/-- New Complex Series Request Message -/
structure NewComplexSeriesRequestMessage where
  clOrdId : BitVec 64
  mpid : Alpha 4
  complexSeriesLegGroup : List ComplexSeriesLegGroup
  deriving DecidableEq, Repr

namespace NewComplexSeriesRequestMessage

def encode (message : NewComplexSeriesRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (Alpha.encode message.mpid
    ++ (encodeMany ComplexSeriesLegGroup.encode message.complexSeriesLegGroup))

def decode (bytes : List UInt8) : Option NewComplexSeriesRequestMessage := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let complexSeriesLegGroup ← decodeAll ComplexSeriesLegGroup.decode bytes.length bytes
  pure { clOrdId, mpid, complexSeriesLegGroup }

theorem encode_length_pos (message : NewComplexSeriesRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : NewComplexSeriesRequestMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany ComplexSeriesLegGroup.encode ComplexSeriesLegGroup.decode ComplexSeriesLegGroup.decode_encode ComplexSeriesLegGroup.encode_length_pos message.complexSeriesLegGroup _ (encodeMany_length_ge ComplexSeriesLegGroup.encode ComplexSeriesLegGroup.encode_length_pos message.complexSeriesLegGroup), some_bind]
  rfl

end NewComplexSeriesRequestMessage

/-- Any Client Sequenced Message, selected by Seq Msg Type -/
inductive ClientSequencedMessage where
  | sessionConfigurationRequestMessage (message : SessionConfigurationRequestMessage) -- 544
  | sequencedFillerMessage (message : SequencedFillerMessage) -- 642
  | newOrderMessage (message : NewOrderMessage) -- 584
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 592
  | orderModifyRequestMessage (message : OrderModifyRequestMessage) -- 593
  | newBulkQuoteType243Message (message : NewBulkQuoteType243Message) -- 579
  | newBulkQuoteType259Message (message : NewBulkQuoteType259Message) -- 601
  | newOrderCrossMessage (message : NewOrderCrossMessage) -- 546
  | bulkCancelRequestType223Message (message : BulkCancelRequestType223Message) -- 547
  | bulkCancelRequestType224Message (message : BulkCancelRequestType224Message) -- 548
  | riskLimitUpdateRequestMessage (message : RiskLimitUpdateRequestMessage) -- 816
  | riskActionRequestMessage (message : RiskActionRequestMessage) -- 817
  | newComplexSeriesRequestMessage (message : NewComplexSeriesRequestMessage) -- 855
  deriving DecidableEq, Repr

namespace ClientSequencedMessage

/-- The Seq Msg Type each message is sent under -/
def tag : ClientSequencedMessage → BitVec 16
  | .sessionConfigurationRequestMessage _ => 544
  | .sequencedFillerMessage _ => 642
  | .newOrderMessage _ => 584
  | .orderCancelRequestMessage _ => 592
  | .orderModifyRequestMessage _ => 593
  | .newBulkQuoteType243Message _ => 579
  | .newBulkQuoteType259Message _ => 601
  | .newOrderCrossMessage _ => 546
  | .bulkCancelRequestType223Message _ => 547
  | .bulkCancelRequestType224Message _ => 548
  | .riskLimitUpdateRequestMessage _ => 816
  | .riskActionRequestMessage _ => 817
  | .newComplexSeriesRequestMessage _ => 855

def encode : ClientSequencedMessage → List UInt8
  | .sessionConfigurationRequestMessage message => SessionConfigurationRequestMessage.encode message
  | .sequencedFillerMessage message => SequencedFillerMessage.encode message
  | .newOrderMessage message => NewOrderMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .orderModifyRequestMessage message => OrderModifyRequestMessage.encode message
  | .newBulkQuoteType243Message message => NewBulkQuoteType243Message.encode message
  | .newBulkQuoteType259Message message => NewBulkQuoteType259Message.encode message
  | .newOrderCrossMessage message => NewOrderCrossMessage.encode message
  | .bulkCancelRequestType223Message message => BulkCancelRequestType223Message.encode message
  | .bulkCancelRequestType224Message message => BulkCancelRequestType224Message.encode message
  | .riskLimitUpdateRequestMessage message => RiskLimitUpdateRequestMessage.encode message
  | .riskActionRequestMessage message => RiskActionRequestMessage.encode message
  | .newComplexSeriesRequestMessage message => NewComplexSeriesRequestMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ClientSequencedMessage :=
  if tag = 544 then (SessionConfigurationRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionConfigurationRequestMessage message) else none
  else if tag = 642 then (SequencedFillerMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedFillerMessage message) else none
  else if tag = 584 then (NewOrderMessage.decode bytes).map fun message => .newOrderMessage message
  else if tag = 592 then (OrderCancelRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderCancelRequestMessage message) else none
  else if tag = 593 then (OrderModifyRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderModifyRequestMessage message) else none
  else if tag = 579 then (NewBulkQuoteType243Message.decode bytes).map fun message => .newBulkQuoteType243Message message
  else if tag = 601 then (NewBulkQuoteType259Message.decode bytes).map fun message => .newBulkQuoteType259Message message
  else if tag = 546 then (NewOrderCrossMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.newOrderCrossMessage message) else none
  else if tag = 547 then (BulkCancelRequestType223Message.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bulkCancelRequestType223Message message) else none
  else if tag = 548 then (BulkCancelRequestType224Message.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bulkCancelRequestType224Message message) else none
  else if tag = 816 then (RiskLimitUpdateRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskLimitUpdateRequestMessage message) else none
  else if tag = 817 then (RiskActionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskActionRequestMessage message) else none
  else if tag = 855 then (NewComplexSeriesRequestMessage.decode bytes).map fun message => .newComplexSeriesRequestMessage message
  else none

theorem decode_encode (message : ClientSequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sessionConfigurationRequestMessage message => simp [decode, encode, tag, SessionConfigurationRequestMessage.decode_encode_nil]
  | sequencedFillerMessage message => simp [decode, encode, tag, SequencedFillerMessage.decode_encode_nil]
  | newOrderMessage message => simp [decode, encode, tag, NewOrderMessage.decode_encode]
  | orderCancelRequestMessage message => simp [decode, encode, tag, OrderCancelRequestMessage.decode_encode_nil]
  | orderModifyRequestMessage message => simp [decode, encode, tag, OrderModifyRequestMessage.decode_encode_nil]
  | newBulkQuoteType243Message message => simp [decode, encode, tag, NewBulkQuoteType243Message.decode_encode]
  | newBulkQuoteType259Message message => simp [decode, encode, tag, NewBulkQuoteType259Message.decode_encode]
  | newOrderCrossMessage message => simp [decode, encode, tag, NewOrderCrossMessage.decode_encode_nil]
  | bulkCancelRequestType223Message message => simp [decode, encode, tag, BulkCancelRequestType223Message.decode_encode_nil]
  | bulkCancelRequestType224Message message => simp [decode, encode, tag, BulkCancelRequestType224Message.decode_encode_nil]
  | riskLimitUpdateRequestMessage message => simp [decode, encode, tag, RiskLimitUpdateRequestMessage.decode_encode_nil]
  | riskActionRequestMessage message => simp [decode, encode, tag, RiskActionRequestMessage.decode_encode_nil]
  | newComplexSeriesRequestMessage message => simp [decode, encode, tag, NewComplexSeriesRequestMessage.decode_encode]

end ClientSequencedMessage

/-- Client Seq Msg: the body, which the record carries with the proof it fits its frame -/
structure ClientSeqMsgBody where
  seqMsgId : SeqMsgId
  reserved4 : Alpha 4
  timestamp : BitVec 64
  seqMsgLength : BitVec 16
  clientSequencedMessage : ClientSequencedMessage
  deriving DecidableEq, Repr

namespace ClientSeqMsgBody

def encodeBody (message : ClientSeqMsgBody) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 (ClientSequencedMessage.tag message.clientSequencedMessage)
    ++ (encodeUIntLE 2 message.seqMsgLength
    ++ (ClientSequencedMessage.encode message.clientSequencedMessage)))))

def decodeBody (bytes : List UInt8) : Option ClientSeqMsgBody := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let clientSequencedMessage ← ClientSequencedMessage.decode seqMsgType bytes
  pure { seqMsgId, reserved4, timestamp, seqMsgLength, clientSequencedMessage }

theorem decodeBody_encodeBody (message : ClientSeqMsgBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [SeqMsgId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientSequencedMessage.decode_encode, some_bind]
  rfl

end ClientSeqMsgBody

/-- Client Seq Msg: the body with the proof its encoding fits Msg Length, whose 2 bytes no bound of the fields fits -/
abbrev ClientSeqMsg := Fitting ClientSeqMsgBody.encodeBody 4 65536

namespace ClientSeqMsg

def encode (message : ClientSeqMsg) : List UInt8 :=
  encodeFramedLE 2 4 ClientSeqMsgBody.encodeBody message.val

def decode : List UInt8 → Option (ClientSeqMsg × List UInt8) :=
  decodeFittingAllLE 2 4 ClientSeqMsgBody.encodeBody ClientSeqMsgBody.decodeBody

@[simp] theorem decode_encode (message : ClientSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 4 ClientSeqMsgBody.encodeBody ClientSeqMsgBody.decodeBody message (ClientSeqMsgBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ClientSeqMsg) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ClientSeqMsg) : (encode message).length ≤ 65533 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
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

end Omi.NyseAmexoptionsBinarygatewayPillarstreamV325ClientPillarMessage
