import Wire

/-!
# New York Stock Exchange Binary Gateway v3.27

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsBinarygatewayPillarstreamV327ServerPillarMessage

/-- Underlying Type: one byte code -/
def UnderlyingType.codes : List UInt8 :=
  [0x41, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4D, 0x4C, 0x4E, 0x4F, 0x50, 0x52, 0x53, 0x54, 0x55, 0x57, 0x58, 0x5A]

inductive UnderlyingType where
  | adr -- Adr
  | commonStock -- Common Stock
  | debentures -- Debentures
  | etf -- Etf
  | foreign -- Foreign
  | ads -- Ads
  | units -- Units
  | miscellaneous -- Miscellaneous
  | indexLinkedNotes -- Index Linked Notes
  | bonds -- Bonds
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | beneficiaryInterest -- Beneficiary Interest
  | structuredNotes -- Structured Notes
  | closedEndFund -- Closed End Fund
  | warrant -- Warrant
  | index -- Index
  | options -- Options
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingType

def toByte : UnderlyingType → UInt8
  | .adr => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .etf => 0x45
  | .foreign => 0x46
  | .ads => 0x48
  | .units => 0x49
  | .miscellaneous => 0x4D
  | .indexLinkedNotes => 0x4C
  | .bonds => 0x4E
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .beneficiaryInterest => 0x53
  | .structuredNotes => 0x54
  | .closedEndFund => 0x55
  | .warrant => 0x57
  | .index => 0x58
  | .options => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingType :=
  if byte = 0x41 then .adr
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .etf
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .ads
  else if byte = 0x49 then .units
  else if byte = 0x4D then .miscellaneous
  else if byte = 0x4C then .indexLinkedNotes
  else if byte = 0x4E then .bonds
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .beneficiaryInterest
  else if byte = 0x54 then .structuredNotes
  else if byte = 0x55 then .closedEndFund
  else if byte = 0x57 then .warrant
  else if byte = 0x58 then .index
  else .options

def ofByte (byte : UInt8) : UnderlyingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingType) : ofByte value.toByte = value := by
  cases value with
  | adr => decide
  | commonStock => decide
  | debentures => decide
  | etf => decide
  | foreign => decide
  | ads => decide
  | units => decide
  | miscellaneous => decide
  | indexLinkedNotes => decide
  | bonds => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | beneficiaryInterest => decide
  | structuredNotes => decide
  | closedEndFund => decide
  | warrant => decide
  | index => decide
  | options => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingType

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

/-- Underlying Symbol Reference Data Message: 54 bytes -/
structure UnderlyingSymbolReferenceDataMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  nyseSymbol : Alpha 24
  listedMic : Alpha 4
  underlyingType : UnderlyingType
  maxOrderPrice : BitVec 64
  mpvClassId : BitVec 16
  testSymbolIndicator : BitVec 8
  channelId : BitVec 8
  legalWidthMultiplier : BitVec 8
  deriving DecidableEq, Repr

namespace UnderlyingSymbolReferenceDataMessage

def encode (message : UnderlyingSymbolReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.nyseSymbol
    ++ (Alpha.encode message.listedMic
    ++ (UnderlyingType.encode message.underlyingType
    ++ (encodeUIntLE 8 message.maxOrderPrice
    ++ (encodeUIntLE 2 message.mpvClassId
    ++ (encodeUIntLE 1 message.testSymbolIndicator
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 1 message.legalWidthMultiplier)))))))))

def decode (bytes : List UInt8) : Option (UnderlyingSymbolReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (nyseSymbol, bytes) ← Alpha.decode 24 bytes
  let (listedMic, bytes) ← Alpha.decode 4 bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (maxOrderPrice, bytes) ← decodeUIntLE 8 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  let (testSymbolIndicator, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (legalWidthMultiplier, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, nyseSymbol, listedMic, underlyingType, maxOrderPrice, mpvClassId, testSymbolIndicator, channelId, legalWidthMultiplier }, bytes)

@[simp] theorem encode_length (message : UnderlyingSymbolReferenceDataMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, UnderlyingType.encode_length]

theorem encode_length_pos (message : UnderlyingSymbolReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingSymbolReferenceDataMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
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
theorem decode_encode_nil (message : UnderlyingSymbolReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnderlyingSymbolReferenceDataMessage

/-- Series Reference Data Message: 63 bytes -/
structure SeriesReferenceDataMessage where
  transactTime : BitVec 64
  seriesIndex : BitVec 32
  symbolId : BitVec 32
  occSymbolRoot : Alpha 24
  putOrCall : BitVec 8
  strikePrice : BitVec 64
  maturityDate : Alpha 8
  contractMultiplier : BitVec 32
  seriesType : BitVec 8
  closingOnlyIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SeriesReferenceDataMessage

def encode (message : SeriesReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.occSymbolRoot
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 4 message.contractMultiplier
    ++ (encodeUIntLE 1 message.seriesType
    ++ (encodeUIntLE 1 message.closingOnlyIndicator)))))))))

def decode (bytes : List UInt8) : Option (SeriesReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (occSymbolRoot, bytes) ← Alpha.decode 24 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (seriesType, bytes) ← decodeUIntLE 1 bytes
  let (closingOnlyIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, seriesIndex, symbolId, occSymbolRoot, putOrCall, strikePrice, maturityDate, contractMultiplier, seriesType, closingOnlyIndicator }, bytes)

@[simp] theorem encode_length (message : SeriesReferenceDataMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesReferenceDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SeriesReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SeriesReferenceDataMessage

/-- Minimum Price Variant Class Reference Data Message: 46 bytes -/
structure MinimumPriceVariantClassReferenceDataMessage where
  transactTime : BitVec 64
  mpvClassName : Alpha 20
  mpvClassId : BitVec 16
  rpimpv : BitVec 64
  luldmpv : BitVec 64
  deriving DecidableEq, Repr

namespace MinimumPriceVariantClassReferenceDataMessage

def encode (message : MinimumPriceVariantClassReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.mpvClassName
    ++ (encodeUIntLE 2 message.mpvClassId
    ++ (encodeUIntLE 8 message.rpimpv
    ++ (encodeUIntLE 8 message.luldmpv))))

def decode (bytes : List UInt8) : Option (MinimumPriceVariantClassReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpvClassName, bytes) ← Alpha.decode 20 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  let (rpimpv, bytes) ← decodeUIntLE 8 bytes
  let (luldmpv, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, mpvClassName, mpvClassId, rpimpv, luldmpv }, bytes)

@[simp] theorem encode_length (message : MinimumPriceVariantClassReferenceDataMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MinimumPriceVariantClassReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumPriceVariantClassReferenceDataMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MinimumPriceVariantClassReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MinimumPriceVariantClassReferenceDataMessage

/-- Mpv Level Definition: 50 bytes -/
structure MpvLevelDefinition where
  mpvLevelName : Alpha 24
  orderEntryLimitPrice : BitVec 64
  quotingMpv : BitVec 64
  tradingMpv : BitVec 64
  mpvClassId : BitVec 16
  deriving DecidableEq, Repr

namespace MpvLevelDefinition

def encode (message : MpvLevelDefinition) : List UInt8 :=
  Alpha.encode message.mpvLevelName
    ++ (encodeUIntLE 8 message.orderEntryLimitPrice
    ++ (encodeUIntLE 8 message.quotingMpv
    ++ (encodeUIntLE 8 message.tradingMpv
    ++ (encodeUIntLE 2 message.mpvClassId))))

def decode (bytes : List UInt8) : Option (MpvLevelDefinition × List UInt8) := do
  let (mpvLevelName, bytes) ← Alpha.decode 24 bytes
  let (orderEntryLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (quotingMpv, bytes) ← decodeUIntLE 8 bytes
  let (tradingMpv, bytes) ← decodeUIntLE 8 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  pure ({ mpvLevelName, orderEntryLimitPrice, quotingMpv, tradingMpv, mpvClassId }, bytes)

@[simp] theorem encode_length (message : MpvLevelDefinition) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MpvLevelDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MpvLevelDefinition) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MpvLevelDefinition

/-- Minimum Price Variant Level Reference Data Message -/
structure MinimumPriceVariantLevelReferenceDataMessage where
  transactTime : BitVec 64
  mpvLevelDefinition : List MpvLevelDefinition
  deriving DecidableEq, Repr

namespace MinimumPriceVariantLevelReferenceDataMessage

def encode (message : MinimumPriceVariantLevelReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeMany MpvLevelDefinition.encode message.mpvLevelDefinition)

def decode (bytes : List UInt8) : Option MinimumPriceVariantLevelReferenceDataMessage := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let mpvLevelDefinition ← decodeAll MpvLevelDefinition.decode bytes.length bytes
  pure { transactTime, mpvLevelDefinition }

theorem encode_length_pos (message : MinimumPriceVariantLevelReferenceDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

theorem decode_encode (message : MinimumPriceVariantLevelReferenceDataMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeAll_encodeMany MpvLevelDefinition.encode MpvLevelDefinition.decode MpvLevelDefinition.decode_encode MpvLevelDefinition.encode_length_pos message.mpvLevelDefinition _ (encodeMany_length_ge MpvLevelDefinition.encode MpvLevelDefinition.encode_length_pos message.mpvLevelDefinition), some_bind]
  rfl

end MinimumPriceVariantLevelReferenceDataMessage

/-- Mpid Configuration Message: 79 bytes -/
structure MpidConfigurationMessage where
  transactTime : BitVec 64
  mpidStatus : BitVec 8
  mpid : Alpha 4
  username : Alpha 16
  reserved50 : Alpha 50
  deriving DecidableEq, Repr

namespace MpidConfigurationMessage

def encode (message : MpidConfigurationMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.mpidStatus
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.reserved50))))

def decode (bytes : List UInt8) : Option (MpidConfigurationMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpidStatus, bytes) ← decodeUIntLE 1 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (reserved50, bytes) ← Alpha.decode 50 bytes
  pure ({ transactTime, mpidStatus, mpid, username, reserved50 }, bytes)

@[simp] theorem encode_length (message : MpidConfigurationMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MpidConfigurationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MpidConfigurationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MpidConfigurationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MpidConfigurationMessage

/-- Options Market Maker Symbol Appointment Reference Data Message: 102 bytes -/
structure OptionsMarketMakerSymbolAppointmentReferenceDataMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  nyseSymbol : Alpha 24
  marketMaker : Alpha 10
  mpid : Alpha 4
  mmType : BitVec 8
  appointmentStatus : BitVec 8
  reserved50 : Alpha 50
  deriving DecidableEq, Repr

namespace OptionsMarketMakerSymbolAppointmentReferenceDataMessage

def encode (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.nyseSymbol
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 1 message.mmType
    ++ (encodeUIntLE 1 message.appointmentStatus
    ++ (Alpha.encode message.reserved50)))))))

def decode (bytes : List UInt8) : Option (OptionsMarketMakerSymbolAppointmentReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (nyseSymbol, bytes) ← Alpha.decode 24 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mmType, bytes) ← decodeUIntLE 1 bytes
  let (appointmentStatus, bytes) ← decodeUIntLE 1 bytes
  let (reserved50, bytes) ← Alpha.decode 50 bytes
  pure ({ transactTime, symbolId, nyseSymbol, marketMaker, mpid, mmType, appointmentStatus, reserved50 }, bytes)

@[simp] theorem encode_length (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OptionsMarketMakerSymbolAppointmentReferenceDataMessage

/-- Session Configuration Acknowledgement Message: 94 bytes -/
structure SessionConfigurationAcknowledgementMessage where
  transactTime : BitVec 64
  userSessionType : BitVec 8
  userSessionStatus : BitVec 8
  username : Alpha 16
  mic : Alpha 4
  cancelOnDisconnect : BitVec 8
  throttlePreference : BitVec 8
  throttleWindow : BitVec 16
  throttleThreshold : BitVec 16
  symbolEligibility : BitVec 8
  maxOrderQuantity : BitVec 32
  selfTradePrevention : BitVec 8
  orderPriorityUpdateAckSubscription : BitVec 8
  ackStatus : BitVec 8
  boldDesignation : BitVec 8
  reserved49 : Alpha 49
  deriving DecidableEq, Repr

namespace SessionConfigurationAcknowledgementMessage

def encode (message : SessionConfigurationAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.userSessionType
    ++ (encodeUIntLE 1 message.userSessionStatus
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.cancelOnDisconnect
    ++ (encodeUIntLE 1 message.throttlePreference
    ++ (encodeUIntLE 2 message.throttleWindow
    ++ (encodeUIntLE 2 message.throttleThreshold
    ++ (encodeUIntLE 1 message.symbolEligibility
    ++ (encodeUIntLE 4 message.maxOrderQuantity
    ++ (encodeUIntLE 1 message.selfTradePrevention
    ++ (encodeUIntLE 1 message.orderPriorityUpdateAckSubscription
    ++ (encodeUIntLE 1 message.ackStatus
    ++ (encodeUIntLE 1 message.boldDesignation
    ++ (Alpha.encode message.reserved49)))))))))))))))

def decode (bytes : List UInt8) : Option (SessionConfigurationAcknowledgementMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (userSessionType, bytes) ← decodeUIntLE 1 bytes
  let (userSessionStatus, bytes) ← decodeUIntLE 1 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (cancelOnDisconnect, bytes) ← decodeUIntLE 1 bytes
  let (throttlePreference, bytes) ← decodeUIntLE 1 bytes
  let (throttleWindow, bytes) ← decodeUIntLE 2 bytes
  let (throttleThreshold, bytes) ← decodeUIntLE 2 bytes
  let (symbolEligibility, bytes) ← decodeUIntLE 1 bytes
  let (maxOrderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (selfTradePrevention, bytes) ← decodeUIntLE 1 bytes
  let (orderPriorityUpdateAckSubscription, bytes) ← decodeUIntLE 1 bytes
  let (ackStatus, bytes) ← decodeUIntLE 1 bytes
  let (boldDesignation, bytes) ← decodeUIntLE 1 bytes
  let (reserved49, bytes) ← Alpha.decode 49 bytes
  pure ({ transactTime, userSessionType, userSessionStatus, username, mic, cancelOnDisconnect, throttlePreference, throttleWindow, throttleThreshold, symbolEligibility, maxOrderQuantity, selfTradePrevention, orderPriorityUpdateAckSubscription, ackStatus, boldDesignation, reserved49 }, bytes)

@[simp] theorem encode_length (message : SessionConfigurationAcknowledgementMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SessionConfigurationAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionConfigurationAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
theorem decode_encode_nil (message : SessionConfigurationAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionConfigurationAcknowledgementMessage

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

/-- Order And Cancel Replace Acknowledgement Message: 180 bytes -/
structure OrderAndCancelReplaceAcknowledgementMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  bitfieldOrderInstructions : BitVec 128
  price : BitVec 64
  orderQty : BitVec 32
  minQty : BitVec 32
  userData : Alpha 10
  transactTime : BitVec 64
  orderId : BitVec 64
  leavesQty : BitVec 32
  workingPrice : BitVec 64
  workingAwayFromDisplay : BitVec 8
  preLiquidityIndicator : Alpha 4
  reasonCode : BitVec 16
  ackType : BitVec 8
  bitfieldFlowIndicator : BitVec 8
  legOpenClose : BitVec 64
  auctionId : BitVec 64
  optionalOrderAddOn : OptionalOrderAddOn
  deriving DecidableEq, Repr

namespace OrderAndCancelReplaceAcknowledgementMessage

def encode (message : OrderAndCancelReplaceAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 16 message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 8 message.workingPrice
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay
    ++ (Alpha.encode message.preLiquidityIndicator
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (encodeUIntLE 8 message.legOpenClose
    ++ (encodeUIntLE 8 message.auctionId
    ++ (OptionalOrderAddOn.encode message.optionalOrderAddOn))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAndCancelReplaceAcknowledgementMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldOrderInstructions, bytes) ← decodeUIntLE 16 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (workingPrice, bytes) ← decodeUIntLE 8 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  let (preLiquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (legOpenClose, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (optionalOrderAddOn, bytes) ← OptionalOrderAddOn.decode bytes
  pure ({ symbolId, mpid, marketMaker, mpSubId, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, userData, transactTime, orderId, leavesQty, workingPrice, workingAwayFromDisplay, preLiquidityIndicator, reasonCode, ackType, bitfieldFlowIndicator, legOpenClose, auctionId, optionalOrderAddOn }, bytes)

@[simp] theorem encode_length (message : OrderAndCancelReplaceAcknowledgementMessage) : (encode message).length = 180 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OptionalOrderAddOn.encode_length]

theorem encode_length_pos (message : OrderAndCancelReplaceAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAndCancelReplaceAcknowledgementMessage) (rest : List UInt8) :
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
  rw [OptionalOrderAddOn.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderAndCancelReplaceAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderAndCancelReplaceAcknowledgementMessage

/-- Quote Ack Group: 21 bytes -/
structure QuoteAckGroup where
  seriesIndex : BitVec 32
  side : BitVec 8
  ackType : BitVec 8
  price : BitVec 64
  quantity : BitVec 32
  reasonCode : BitVec 16
  workingAwayFromDisplay : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteAckGroup

def encode (message : QuoteAckGroup) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay))))))

def decode (bytes : List UInt8) : Option (QuoteAckGroup × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  pure ({ seriesIndex, side, ackType, price, quantity, reasonCode, workingAwayFromDisplay }, bytes)

@[simp] theorem encode_length (message : QuoteAckGroup) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteAckGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAckGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAckGroup

/-- Bulk Quote Acknowledgment Message -/
structure BulkQuoteAcknowledgmentMessage where
  transactTime : BitVec 64
  mpid : Alpha 4
  marketMaker : Alpha 10
  subId : Alpha 4
  clOrdId : BitVec 64
  bitfieldFlowIndicator : BitVec 8
  selfTradeType : BitVec 8
  groupId : BitVec 32
  quoteAckGroup : Bounded 1 QuoteAckGroup
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgmentMessage

def encode (message : BulkQuoteAcknowledgmentMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.subId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (encodeUIntLE 1 message.selfTradeType
    ++ (encodeUIntLE 4 message.groupId
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.quoteAckGroup.val.length)
    ++ (encodeMany QuoteAckGroup.encode message.quoteAckGroup.val)))))))))

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgmentMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (subId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeType, bytes) ← decodeUIntLE 1 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (repeatingGroups, bytes) ← decodeUIntLE 1 bytes
  let (quoteAckGroup_, bytes) ← decodeMany QuoteAckGroup.decode repeatingGroups.toNat bytes
  if fits_quoteAckGroup : quoteAckGroup_.length < 256 ^ 1 then
    pure ({ transactTime, mpid, marketMaker, subId, clOrdId, bitfieldFlowIndicator, selfTradeType, groupId, quoteAckGroup := ⟨quoteAckGroup_, fits_quoteAckGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteAcknowledgmentMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteAcknowledgmentMessage) : (encode message).length ≤ 5396 := by
  have bound_quoteAckGroup := message.quoteAckGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const QuoteAckGroup.encode 21 QuoteAckGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgmentMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 1 QuoteAckGroup.encode QuoteAckGroup.decode QuoteAckGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteAckGroup.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BulkQuoteAcknowledgmentMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BulkQuoteAcknowledgmentMessage

/-- Quote Ack With Id Group: 29 bytes -/
structure QuoteAckWithIdGroup where
  seriesIndex : BitVec 32
  side : BitVec 8
  ackType : BitVec 8
  price : BitVec 64
  quantity : BitVec 32
  reasonCode : BitVec 16
  workingAwayFromDisplay : BitVec 8
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteAckWithIdGroup

def encode (message : QuoteAckWithIdGroup) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay
    ++ (encodeUIntLE 8 message.orderId)))))))

def decode (bytes : List UInt8) : Option (QuoteAckWithIdGroup × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ seriesIndex, side, ackType, price, quantity, reasonCode, workingAwayFromDisplay, orderId }, bytes)

@[simp] theorem encode_length (message : QuoteAckWithIdGroup) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteAckWithIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAckWithIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAckWithIdGroup

/-- Bulk Quote Acknowledgment With Details Message -/
structure BulkQuoteAcknowledgmentWithDetailsMessage where
  transactTime : BitVec 64
  mpid : Alpha 4
  marketMaker : Alpha 10
  subId : Alpha 4
  clOrdId : BitVec 64
  bitfieldFlowIndicator : BitVec 8
  selfTradeType : BitVec 8
  groupId : BitVec 32
  quoteAckWithIdGroup : Bounded 1 QuoteAckWithIdGroup
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgmentWithDetailsMessage

def encode (message : BulkQuoteAcknowledgmentWithDetailsMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.subId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (encodeUIntLE 1 message.selfTradeType
    ++ (encodeUIntLE 4 message.groupId
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.quoteAckWithIdGroup.val.length)
    ++ (encodeMany QuoteAckWithIdGroup.encode message.quoteAckWithIdGroup.val)))))))))

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgmentWithDetailsMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (subId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeType, bytes) ← decodeUIntLE 1 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (repeatingGroups, bytes) ← decodeUIntLE 1 bytes
  let (quoteAckWithIdGroup_, bytes) ← decodeMany QuoteAckWithIdGroup.decode repeatingGroups.toNat bytes
  if fits_quoteAckWithIdGroup : quoteAckWithIdGroup_.length < 256 ^ 1 then
    pure ({ transactTime, mpid, marketMaker, subId, clOrdId, bitfieldFlowIndicator, selfTradeType, groupId, quoteAckWithIdGroup := ⟨quoteAckWithIdGroup_, fits_quoteAckWithIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteAcknowledgmentWithDetailsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteAcknowledgmentWithDetailsMessage) : (encode message).length ≤ 7436 := by
  have bound_quoteAckWithIdGroup := message.quoteAckWithIdGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const QuoteAckWithIdGroup.encode 29 QuoteAckWithIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgmentWithDetailsMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 1 QuoteAckWithIdGroup.encode QuoteAckWithIdGroup.decode QuoteAckWithIdGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteAckWithIdGroup.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BulkQuoteAcknowledgmentWithDetailsMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BulkQuoteAcknowledgmentWithDetailsMessage

/-- Order Single Complex Modify Cancel Request Acknowledgment And Urout Message: 108 bytes -/
structure OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  refClOrdId : BitVec 64
  origClOrdId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 32
  leavesQty : BitVec 32
  side : BitVec 8
  locateReqd : BitVec 8
  reasonCode : BitVec 16
  ackType : BitVec 8
  bitfieldFlowIndicator : BitVec 8
  userData : Alpha 10
  groupId : BitVec 32
  marketMaker : Alpha 10
  targetCancelUsername : Alpha 16
  targetCancelMpid : Alpha 4
  bulkAction : BitVec 8
  cancelScope : BitVec 8
  deriving DecidableEq, Repr

namespace OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage

def encode (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.refClOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.locateReqd
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 4 message.groupId
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.targetCancelUsername
    ++ (Alpha.encode message.targetCancelMpid
    ++ (encodeUIntLE 1 message.bulkAction
    ++ (encodeUIntLE 1 message.cancelScope))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (refClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (locateReqd, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (targetCancelUsername, bytes) ← Alpha.decode 16 bytes
  let (targetCancelMpid, bytes) ← Alpha.decode 4 bytes
  let (bulkAction, bytes) ← decodeUIntLE 1 bytes
  let (cancelScope, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, mpid, orderId, refClOrdId, origClOrdId, price, orderQty, leavesQty, side, locateReqd, reasonCode, ackType, bitfieldFlowIndicator, userData, groupId, marketMaker, targetCancelUsername, targetCancelMpid, bulkAction, cancelScope }, bytes)

@[simp] theorem encode_length (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage

/-- Order Priority Update Acknowledgment Message: 60 bytes -/
structure OrderPriorityUpdateAcknowledgmentMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  workingPrice : BitVec 64
  orderQty : BitVec 32
  workingAwayFromDisplay : BitVec 8
  preLiquidityIndicator : Alpha 4
  ackType : BitVec 8
  userData : Alpha 10
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateAcknowledgmentMessage

def encode (message : OrderPriorityUpdateAcknowledgmentMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.workingPrice
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay
    ++ (Alpha.encode message.preLiquidityIndicator
    ++ (encodeUIntLE 1 message.ackType
    ++ (Alpha.encode message.userData))))))))))

def decode (bytes : List UInt8) : Option (OrderPriorityUpdateAcknowledgmentMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (workingPrice, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  let (preLiquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  pure ({ transactTime, symbolId, mpid, orderId, clOrdId, workingPrice, orderQty, workingAwayFromDisplay, preLiquidityIndicator, ackType, userData }, bytes)

@[simp] theorem encode_length (message : OrderPriorityUpdateAcknowledgmentMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderPriorityUpdateAcknowledgmentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriorityUpdateAcknowledgmentMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderPriorityUpdateAcknowledgmentMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderPriorityUpdateAcknowledgmentMessage

/-- Execution Report Message: 179 bytes -/
structure ExecutionReportMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  dealId : BitVec 64
  lastPx : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  lastQty : BitVec 32
  liquidityIndicator : Alpha 4
  multilegReportingType : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  locateReqd : BitVec 8
  participantType : BitVec 8
  reasonCode : BitVec 16
  userData : Alpha 10
  side : BitVec 8
  marketMaker : Alpha 10
  contraMarketMaker : Alpha 10
  contraClearingFirm : Alpha 5
  contraMpid : Alpha 4
  contraOpenClose : BitVec 8
  contraCustomerOrFirm : BitVec 8
  contraClearingAccount : Alpha 5
  contraCrossType : BitVec 16
  contraCoveredOrUncovered : BitVec 8
  coveredOrUncovered : BitVec 8
  crossId : BitVec 64
  openClose : BitVec 8
  optionalOrderAddOn : OptionalOrderAddOn
  deriving DecidableEq, Repr

namespace ExecutionReportMessage

def encode (message : ExecutionReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.dealId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.lastQty
    ++ (Alpha.encode message.liquidityIndicator
    ++ (encodeUIntLE 1 message.multilegReportingType
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (encodeUIntLE 1 message.locateReqd
    ++ (encodeUIntLE 1 message.participantType
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.contraMarketMaker
    ++ (Alpha.encode message.contraClearingFirm
    ++ (Alpha.encode message.contraMpid
    ++ (encodeUIntLE 1 message.contraOpenClose
    ++ (encodeUIntLE 1 message.contraCustomerOrFirm
    ++ (Alpha.encode message.contraClearingAccount
    ++ (encodeUIntLE 2 message.contraCrossType
    ++ (encodeUIntLE 1 message.contraCoveredOrUncovered
    ++ (encodeUIntLE 1 message.coveredOrUncovered
    ++ (encodeUIntLE 8 message.crossId
    ++ (encodeUIntLE 1 message.openClose
    ++ (OptionalOrderAddOn.encode message.optionalOrderAddOn)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (dealId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (liquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (multilegReportingType, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (locateReqd, bytes) ← decodeUIntLE 1 bytes
  let (participantType, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (contraMarketMaker, bytes) ← Alpha.decode 10 bytes
  let (contraClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (contraMpid, bytes) ← Alpha.decode 4 bytes
  let (contraOpenClose, bytes) ← decodeUIntLE 1 bytes
  let (contraCustomerOrFirm, bytes) ← decodeUIntLE 1 bytes
  let (contraClearingAccount, bytes) ← Alpha.decode 5 bytes
  let (contraCrossType, bytes) ← decodeUIntLE 2 bytes
  let (contraCoveredOrUncovered, bytes) ← decodeUIntLE 1 bytes
  let (coveredOrUncovered, bytes) ← decodeUIntLE 1 bytes
  let (crossId, bytes) ← decodeUIntLE 8 bytes
  let (openClose, bytes) ← decodeUIntLE 1 bytes
  let (optionalOrderAddOn, bytes) ← OptionalOrderAddOn.decode bytes
  pure ({ transactTime, symbolId, mpid, orderId, clOrdId, dealId, lastPx, leavesQty, cumQty, lastQty, liquidityIndicator, multilegReportingType, reserved1, reserved2, locateReqd, participantType, reasonCode, userData, side, marketMaker, contraMarketMaker, contraClearingFirm, contraMpid, contraOpenClose, contraCustomerOrFirm, contraClearingAccount, contraCrossType, contraCoveredOrUncovered, coveredOrUncovered, crossId, openClose, optionalOrderAddOn }, bytes)

@[simp] theorem encode_length (message : ExecutionReportMessage) : (encode message).length = 179 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OptionalOrderAddOn.encode_length]

theorem encode_length_pos (message : ExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OptionalOrderAddOn.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ExecutionReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ExecutionReportMessage

/-- Ref Seq Msg Id: 16 bytes -/
structure RefSeqMsgId where
  streamId : StreamId
  seq : BitVec 64
  deriving DecidableEq, Repr

namespace RefSeqMsgId

def encode (message : RefSeqMsgId) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.seq)

def decode (bytes : List UInt8) : Option (RefSeqMsgId × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (seq, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamId, seq }, bytes)

@[simp] theorem encode_length (message : RefSeqMsgId) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, StreamId.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RefSeqMsgId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefSeqMsgId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefSeqMsgId

/-- Trade Bust Correct Message: 81 bytes -/
structure TradeBustCorrectMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  refSeqMsgId : RefSeqMsgId
  dealId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 32
  reasonCode : BitVec 16
  userData : Alpha 10
  bustCorrectIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TradeBustCorrectMessage

def encode (message : TradeBustCorrectMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (RefSeqMsgId.encode message.refSeqMsgId
    ++ (encodeUIntLE 8 message.dealId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 1 message.bustCorrectIndicator)))))))))))

def decode (bytes : List UInt8) : Option (TradeBustCorrectMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (refSeqMsgId, bytes) ← RefSeqMsgId.decode bytes
  let (dealId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (bustCorrectIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, mpid, orderId, clOrdId, refSeqMsgId, dealId, lastPx, lastQty, reasonCode, userData, bustCorrectIndicator }, bytes)

@[simp] theorem encode_length (message : TradeBustCorrectMessage) : (encode message).length = 81 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RefSeqMsgId.encode_length]

theorem encode_length_pos (message : TradeBustCorrectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustCorrectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, RefSeqMsgId.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeBustCorrectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeBustCorrectMessage

/-- Application Layer Reject Message: 41 bytes -/
structure ApplicationLayerRejectMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  reasonCode : BitVec 16
  rejectType : BitVec 8
  userData : Alpha 10
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace ApplicationLayerRejectMessage

def encode (message : ApplicationLayerRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.rejectType
    ++ (Alpha.encode message.userData
    ++ (Alpha.encode message.reserved4)))))))

def decode (bytes : List UInt8) : Option (ApplicationLayerRejectMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectType, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 10 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ transactTime, symbolId, mpid, clOrdId, reasonCode, rejectType, userData, reserved4 }, bytes)

@[simp] theorem encode_length (message : ApplicationLayerRejectMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ApplicationLayerRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApplicationLayerRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ApplicationLayerRejectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ApplicationLayerRejectMessage

/-- Risk Control Acknowledgement Message: 310 bytes -/
structure RiskControlAcknowledgementMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskAckType : BitVec 8
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskControlActivation : BitVec 8
  riskActionType : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionResponse : BitVec 8
  iocAttribution : BitVec 8
  usdCalculation1 : BitVec 64
  usdCalculation2 : BitVec 64
  usdCalculation3 : BitVec 64
  usdCalculation4 : BitVec 64
  countCalculation : BitVec 32
  blockedByBreachIndicator : BitVec 8
  blockedByKillSwitchIndicator : BitVec 8
  reinstatementRequiredBySelf : BitVec 8
  reinstatementRequiredByOther : BitVec 8
  riskRangeId : BitVec 8
  riskMinimumValue : BitVec 64
  priceScale : BitVec 8
  reserved190 : Alpha 190
  deriving DecidableEq, Repr

namespace RiskControlAcknowledgementMessage

def encode (message : RiskControlAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.riskAckType
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskControlActivation
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionResponse
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 8 message.usdCalculation1
    ++ (encodeUIntLE 8 message.usdCalculation2
    ++ (encodeUIntLE 8 message.usdCalculation3
    ++ (encodeUIntLE 8 message.usdCalculation4
    ++ (encodeUIntLE 4 message.countCalculation
    ++ (encodeUIntLE 1 message.blockedByBreachIndicator
    ++ (encodeUIntLE 1 message.blockedByKillSwitchIndicator
    ++ (encodeUIntLE 1 message.reinstatementRequiredBySelf
    ++ (encodeUIntLE 1 message.reinstatementRequiredByOther
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (encodeUIntLE 8 message.riskMinimumValue
    ++ (encodeUIntLE 1 message.priceScale
    ++ (Alpha.encode message.reserved190)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RiskControlAcknowledgementMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskAckType, bytes) ← decodeUIntLE 1 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskControlActivation, bytes) ← decodeUIntLE 1 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionResponse, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (usdCalculation1, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation2, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation3, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation4, bytes) ← decodeUIntLE 8 bytes
  let (countCalculation, bytes) ← decodeUIntLE 4 bytes
  let (blockedByBreachIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockedByKillSwitchIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredBySelf, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredByOther, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (riskMinimumValue, bytes) ← decodeUIntLE 8 bytes
  let (priceScale, bytes) ← decodeUIntLE 1 bytes
  let (reserved190, bytes) ← Alpha.decode 190 bytes
  pure ({ symbolId, mpid, marketMaker, mpSubId, reserved4, clearingNumber, clOrdId, riskAckType, riskUserCrd, riskUserType, riskControlType, riskControlActivation, riskActionType, usdLimit, timeLimit, percentageLimit, countLimit, breachActionResponse, iocAttribution, usdCalculation1, usdCalculation2, usdCalculation3, usdCalculation4, countCalculation, blockedByBreachIndicator, blockedByKillSwitchIndicator, reinstatementRequiredBySelf, reinstatementRequiredByOther, riskRangeId, riskMinimumValue, priceScale, reserved190 }, bytes)

@[simp] theorem encode_length (message : RiskControlAcknowledgementMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskControlAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RiskControlAcknowledgementMessage) (rest : List UInt8) :
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
theorem decode_encode_nil (message : RiskControlAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskControlAcknowledgementMessage

/-- Risk Control Alert Message: 301 bytes -/
structure RiskControlAlertMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMaker : Alpha 10
  mpSubId : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionResponse : BitVec 8
  iocAttribution : BitVec 8
  usdCalculation1 : BitVec 64
  usdCalculation2 : BitVec 64
  usdCalculation3 : BitVec 64
  usdCalculation4 : BitVec 64
  countCalculation : BitVec 32
  riskActionType : BitVec 8
  thresholdBreachLevel : BitVec 8
  blockedByBreachIndicator : BitVec 8
  blockedByKillSwitchIndicator : BitVec 8
  reinstatementRequiredBySelf : BitVec 8
  reinstatementRequiredByOther : BitVec 8
  reserved200 : Alpha 200
  deriving DecidableEq, Repr

namespace RiskControlAlertMessage

def encode (message : RiskControlAlertMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.mpSubId
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionResponse
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 8 message.usdCalculation1
    ++ (encodeUIntLE 8 message.usdCalculation2
    ++ (encodeUIntLE 8 message.usdCalculation3
    ++ (encodeUIntLE 8 message.usdCalculation4
    ++ (encodeUIntLE 4 message.countCalculation
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 1 message.thresholdBreachLevel
    ++ (encodeUIntLE 1 message.blockedByBreachIndicator
    ++ (encodeUIntLE 1 message.blockedByKillSwitchIndicator
    ++ (encodeUIntLE 1 message.reinstatementRequiredBySelf
    ++ (encodeUIntLE 1 message.reinstatementRequiredByOther
    ++ (Alpha.encode message.reserved200))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RiskControlAlertMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mpSubId, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionResponse, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (usdCalculation1, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation2, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation3, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation4, bytes) ← decodeUIntLE 8 bytes
  let (countCalculation, bytes) ← decodeUIntLE 4 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (thresholdBreachLevel, bytes) ← decodeUIntLE 1 bytes
  let (blockedByBreachIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockedByKillSwitchIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredBySelf, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredByOther, bytes) ← decodeUIntLE 1 bytes
  let (reserved200, bytes) ← Alpha.decode 200 bytes
  pure ({ symbolId, mpid, marketMaker, mpSubId, reserved4, clearingNumber, riskUserCrd, riskUserType, riskControlType, usdLimit, timeLimit, percentageLimit, countLimit, breachActionResponse, iocAttribution, usdCalculation1, usdCalculation2, usdCalculation3, usdCalculation4, countCalculation, riskActionType, thresholdBreachLevel, blockedByBreachIndicator, blockedByKillSwitchIndicator, reinstatementRequiredBySelf, reinstatementRequiredByOther, reserved200 }, bytes)

@[simp] theorem encode_length (message : RiskControlAlertMessage) : (encode message).length = 301 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskControlAlertMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RiskControlAlertMessage) (rest : List UInt8) :
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
theorem decode_encode_nil (message : RiskControlAlertMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskControlAlertMessage

/-- Leg Group: 7 bytes -/
structure LegGroup where
  legSymbolId : BitVec 32
  legRatioQty : BitVec 16
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace LegGroup

def encode (message : LegGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSymbolId
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (encodeUIntLE 1 message.legSide))

def decode (bytes : List UInt8) : Option (LegGroup × List UInt8) := do
  let (legSymbolId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← decodeUIntLE 1 bytes
  pure ({ legSymbolId, legRatioQty, legSide }, bytes)

@[simp] theorem encode_length (message : LegGroup) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LegGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LegGroup

/-- Complex Series Request Acknowledgement Message -/
structure ComplexSeriesRequestAcknowledgementMessage where
  transactTime : BitVec 64
  clOrdId : BitVec 64
  reasonCode : BitVec 16
  symbolId : BitVec 32
  side : BitVec 8
  legGroup : Bounded 1 LegGroup
  deriving DecidableEq, Repr

namespace ComplexSeriesRequestAcknowledgementMessage

def encode (message : ComplexSeriesRequestAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.legGroup.val.length)
    ++ (encodeMany LegGroup.encode message.legGroup.val))))))

def decode (bytes : List UInt8) : Option (ComplexSeriesRequestAcknowledgementMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (repeatingGroups, bytes) ← decodeUIntLE 1 bytes
  let (legGroup_, bytes) ← decodeMany LegGroup.decode repeatingGroups.toNat bytes
  if fits_legGroup : legGroup_.length < 256 ^ 1 then
    pure ({ transactTime, clOrdId, reasonCode, symbolId, side, legGroup := ⟨legGroup_, fits_legGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexSeriesRequestAcknowledgementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexSeriesRequestAcknowledgementMessage) : (encode message).length ≤ 1809 := by
  have bound_legGroup := message.legGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const LegGroup.encode 7 LegGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexSeriesRequestAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeMany_bounded 1 LegGroup.encode LegGroup.decode LegGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legGroup.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ComplexSeriesRequestAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ComplexSeriesRequestAcknowledgementMessage

/-- Any Server Sequenced Message, selected by Seq Msg Type -/
inductive ServerSequencedMessage where
  | underlyingSymbolReferenceDataMessage (message : UnderlyingSymbolReferenceDataMessage) -- 563
  | seriesReferenceDataMessage (message : SeriesReferenceDataMessage) -- 564
  | minimumPriceVariantClassReferenceDataMessage (message : MinimumPriceVariantClassReferenceDataMessage) -- 560
  | minimumPriceVariantLevelReferenceDataMessage (message : MinimumPriceVariantLevelReferenceDataMessage) -- 561
  | mpidConfigurationMessage (message : MpidConfigurationMessage) -- 626
  | optionsMarketMakerSymbolAppointmentReferenceDataMessage (message : OptionsMarketMakerSymbolAppointmentReferenceDataMessage) -- 2099
  | sessionConfigurationAcknowledgementMessage (message : SessionConfigurationAcknowledgementMessage) -- 545
  | orderAndCancelReplaceAcknowledgementMessage (message : OrderAndCancelReplaceAcknowledgementMessage) -- 617
  | bulkQuoteAcknowledgmentMessage (message : BulkQuoteAcknowledgmentMessage) -- 660
  | bulkQuoteAcknowledgmentWithDetailsMessage (message : BulkQuoteAcknowledgmentWithDetailsMessage) -- 776
  | orderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage (message : OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage) -- 632
  | orderPriorityUpdateAcknowledgmentMessage (message : OrderPriorityUpdateAcknowledgmentMessage) -- 616
  | executionReportMessage (message : ExecutionReportMessage) -- 661
  | tradeBustCorrectMessage (message : TradeBustCorrectMessage) -- 659
  | applicationLayerRejectMessage (message : ApplicationLayerRejectMessage) -- 615
  | riskControlAcknowledgementMessage (message : RiskControlAcknowledgementMessage) -- 818
  | riskControlAlertMessage (message : RiskControlAlertMessage) -- 819
  | complexSeriesRequestAcknowledgementMessage (message : ComplexSeriesRequestAcknowledgementMessage) -- 856
  deriving DecidableEq, Repr

namespace ServerSequencedMessage

/-- The Seq Msg Type each message is sent under -/
def tag : ServerSequencedMessage → BitVec 16
  | .underlyingSymbolReferenceDataMessage _ => 563
  | .seriesReferenceDataMessage _ => 564
  | .minimumPriceVariantClassReferenceDataMessage _ => 560
  | .minimumPriceVariantLevelReferenceDataMessage _ => 561
  | .mpidConfigurationMessage _ => 626
  | .optionsMarketMakerSymbolAppointmentReferenceDataMessage _ => 2099
  | .sessionConfigurationAcknowledgementMessage _ => 545
  | .orderAndCancelReplaceAcknowledgementMessage _ => 617
  | .bulkQuoteAcknowledgmentMessage _ => 660
  | .bulkQuoteAcknowledgmentWithDetailsMessage _ => 776
  | .orderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage _ => 632
  | .orderPriorityUpdateAcknowledgmentMessage _ => 616
  | .executionReportMessage _ => 661
  | .tradeBustCorrectMessage _ => 659
  | .applicationLayerRejectMessage _ => 615
  | .riskControlAcknowledgementMessage _ => 818
  | .riskControlAlertMessage _ => 819
  | .complexSeriesRequestAcknowledgementMessage _ => 856

def encode : ServerSequencedMessage → List UInt8
  | .underlyingSymbolReferenceDataMessage message => UnderlyingSymbolReferenceDataMessage.encode message
  | .seriesReferenceDataMessage message => SeriesReferenceDataMessage.encode message
  | .minimumPriceVariantClassReferenceDataMessage message => MinimumPriceVariantClassReferenceDataMessage.encode message
  | .minimumPriceVariantLevelReferenceDataMessage message => MinimumPriceVariantLevelReferenceDataMessage.encode message
  | .mpidConfigurationMessage message => MpidConfigurationMessage.encode message
  | .optionsMarketMakerSymbolAppointmentReferenceDataMessage message => OptionsMarketMakerSymbolAppointmentReferenceDataMessage.encode message
  | .sessionConfigurationAcknowledgementMessage message => SessionConfigurationAcknowledgementMessage.encode message
  | .orderAndCancelReplaceAcknowledgementMessage message => OrderAndCancelReplaceAcknowledgementMessage.encode message
  | .bulkQuoteAcknowledgmentMessage message => BulkQuoteAcknowledgmentMessage.encode message
  | .bulkQuoteAcknowledgmentWithDetailsMessage message => BulkQuoteAcknowledgmentWithDetailsMessage.encode message
  | .orderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage message => OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage.encode message
  | .orderPriorityUpdateAcknowledgmentMessage message => OrderPriorityUpdateAcknowledgmentMessage.encode message
  | .executionReportMessage message => ExecutionReportMessage.encode message
  | .tradeBustCorrectMessage message => TradeBustCorrectMessage.encode message
  | .applicationLayerRejectMessage message => ApplicationLayerRejectMessage.encode message
  | .riskControlAcknowledgementMessage message => RiskControlAcknowledgementMessage.encode message
  | .riskControlAlertMessage message => RiskControlAlertMessage.encode message
  | .complexSeriesRequestAcknowledgementMessage message => ComplexSeriesRequestAcknowledgementMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerSequencedMessage :=
  if tag = 563 then (UnderlyingSymbolReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.underlyingSymbolReferenceDataMessage message) else none
  else if tag = 564 then (SeriesReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.seriesReferenceDataMessage message) else none
  else if tag = 560 then (MinimumPriceVariantClassReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.minimumPriceVariantClassReferenceDataMessage message) else none
  else if tag = 561 then (MinimumPriceVariantLevelReferenceDataMessage.decode bytes).map fun message => .minimumPriceVariantLevelReferenceDataMessage message
  else if tag = 626 then (MpidConfigurationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mpidConfigurationMessage message) else none
  else if tag = 2099 then (OptionsMarketMakerSymbolAppointmentReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.optionsMarketMakerSymbolAppointmentReferenceDataMessage message) else none
  else if tag = 545 then (SessionConfigurationAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionConfigurationAcknowledgementMessage message) else none
  else if tag = 617 then (OrderAndCancelReplaceAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderAndCancelReplaceAcknowledgementMessage message) else none
  else if tag = 660 then (BulkQuoteAcknowledgmentMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bulkQuoteAcknowledgmentMessage message) else none
  else if tag = 776 then (BulkQuoteAcknowledgmentWithDetailsMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bulkQuoteAcknowledgmentWithDetailsMessage message) else none
  else if tag = 632 then (OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage message) else none
  else if tag = 616 then (OrderPriorityUpdateAcknowledgmentMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderPriorityUpdateAcknowledgmentMessage message) else none
  else if tag = 661 then (ExecutionReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.executionReportMessage message) else none
  else if tag = 659 then (TradeBustCorrectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBustCorrectMessage message) else none
  else if tag = 615 then (ApplicationLayerRejectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.applicationLayerRejectMessage message) else none
  else if tag = 818 then (RiskControlAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskControlAcknowledgementMessage message) else none
  else if tag = 819 then (RiskControlAlertMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskControlAlertMessage message) else none
  else if tag = 856 then (ComplexSeriesRequestAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.complexSeriesRequestAcknowledgementMessage message) else none
  else none

theorem decode_encode (message : ServerSequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | underlyingSymbolReferenceDataMessage message => simp [decode, encode, tag, UnderlyingSymbolReferenceDataMessage.decode_encode_nil]
  | seriesReferenceDataMessage message => simp [decode, encode, tag, SeriesReferenceDataMessage.decode_encode_nil]
  | minimumPriceVariantClassReferenceDataMessage message => simp [decode, encode, tag, MinimumPriceVariantClassReferenceDataMessage.decode_encode_nil]
  | minimumPriceVariantLevelReferenceDataMessage message => simp [decode, encode, tag, MinimumPriceVariantLevelReferenceDataMessage.decode_encode]
  | mpidConfigurationMessage message => simp [decode, encode, tag, MpidConfigurationMessage.decode_encode_nil]
  | optionsMarketMakerSymbolAppointmentReferenceDataMessage message => simp [decode, encode, tag, OptionsMarketMakerSymbolAppointmentReferenceDataMessage.decode_encode_nil]
  | sessionConfigurationAcknowledgementMessage message => simp [decode, encode, tag, SessionConfigurationAcknowledgementMessage.decode_encode_nil]
  | orderAndCancelReplaceAcknowledgementMessage message => simp [decode, encode, tag, OrderAndCancelReplaceAcknowledgementMessage.decode_encode_nil]
  | bulkQuoteAcknowledgmentMessage message => simp [decode, encode, tag, BulkQuoteAcknowledgmentMessage.decode_encode_nil]
  | bulkQuoteAcknowledgmentWithDetailsMessage message => simp [decode, encode, tag, BulkQuoteAcknowledgmentWithDetailsMessage.decode_encode_nil]
  | orderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage message => simp [decode, encode, tag, OrderSingleComplexModifyCancelRequestAcknowledgmentAndUroutMessage.decode_encode_nil]
  | orderPriorityUpdateAcknowledgmentMessage message => simp [decode, encode, tag, OrderPriorityUpdateAcknowledgmentMessage.decode_encode_nil]
  | executionReportMessage message => simp [decode, encode, tag, ExecutionReportMessage.decode_encode_nil]
  | tradeBustCorrectMessage message => simp [decode, encode, tag, TradeBustCorrectMessage.decode_encode_nil]
  | applicationLayerRejectMessage message => simp [decode, encode, tag, ApplicationLayerRejectMessage.decode_encode_nil]
  | riskControlAcknowledgementMessage message => simp [decode, encode, tag, RiskControlAcknowledgementMessage.decode_encode_nil]
  | riskControlAlertMessage message => simp [decode, encode, tag, RiskControlAlertMessage.decode_encode_nil]
  | complexSeriesRequestAcknowledgementMessage message => simp [decode, encode, tag, ComplexSeriesRequestAcknowledgementMessage.decode_encode_nil]

end ServerSequencedMessage

/-- Server Seq Msg: the body, which the record carries with the proof it fits its frame -/
structure ServerSeqMsgBody where
  seqMsgId : SeqMsgId
  reserved4 : Alpha 4
  timestamp : BitVec 64
  seqMsgLength : BitVec 16
  serverSequencedMessage : ServerSequencedMessage
  deriving DecidableEq, Repr

namespace ServerSeqMsgBody

def encodeBody (message : ServerSeqMsgBody) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 (ServerSequencedMessage.tag message.serverSequencedMessage)
    ++ (encodeUIntLE 2 message.seqMsgLength
    ++ (ServerSequencedMessage.encode message.serverSequencedMessage)))))

def decodeBody (bytes : List UInt8) : Option ServerSeqMsgBody := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let serverSequencedMessage ← ServerSequencedMessage.decode seqMsgType bytes
  pure { seqMsgId, reserved4, timestamp, seqMsgLength, serverSequencedMessage }

theorem decodeBody_encodeBody (message : ServerSeqMsgBody) : decodeBody (encodeBody message) = some message := by
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
  rw [ServerSequencedMessage.decode_encode, some_bind]
  rfl

end ServerSeqMsgBody

/-- Server Seq Msg: the body with the proof its encoding fits Msg Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerSeqMsg := Fitting ServerSeqMsgBody.encodeBody 4 65536

namespace ServerSeqMsg

def encode (message : ServerSeqMsg) : List UInt8 :=
  encodeFramedLE 2 4 ServerSeqMsgBody.encodeBody message.val

def decode : List UInt8 → Option (ServerSeqMsg × List UInt8) :=
  decodeFittingAllLE 2 4 ServerSeqMsgBody.encodeBody ServerSeqMsgBody.decodeBody

@[simp] theorem decode_encode (message : ServerSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 4 ServerSeqMsgBody.encodeBody ServerSeqMsgBody.decodeBody message (ServerSeqMsgBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerSeqMsg) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerSeqMsg) : (encode message).length ≤ 65533 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
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

end Omi.NyseArcaoptionsBinarygatewayPillarstreamV327ServerPillarMessage
