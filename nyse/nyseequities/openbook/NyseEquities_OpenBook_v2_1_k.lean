import Wire

/-!
# New York Stock Exchange Open Book v2.1.k

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNyseequitiesOpenbookUltraV21K

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x41, 0x52]

inductive Status where
  | accepted -- Accepted
  | rejected -- Rejected
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .accepted => 0x41
  | .rejected => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x41 then .accepted
  else .rejected

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | accepted => decide
  | rejected => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Status) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Reject Reason: one byte code -/
def RejectReason.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive RejectReason where
  | requestAccepted -- Request Accepted
  | rejectedDueToPermissions -- Rejected Due To Permissions
  | invalidSequenceRangeEgLowHigh -- Invalid Sequence Range Eg Low High
  | exceededMaxSequenceRange1000 -- Exceeded Max Sequence Range 1000
  | exceededMaxRetransRequestsInADay -- Exceeded Max Retrans Requests In A Day
  | exceededMaxRefreshRequestsInADay -- Exceeded Max Refresh Requests In A Day
  | rejectedRequestedSeqnum1000000PacketsInThePastUseRefreshToRecoverCurrentStateIfNecessary -- Rejected Requested Seqnum 1000000 Packets In The Past Use Refresh To Recover Current State If Necessary
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReason

def toByte : RejectReason → UInt8
  | .requestAccepted => 0x30
  | .rejectedDueToPermissions => 0x31
  | .invalidSequenceRangeEgLowHigh => 0x32
  | .exceededMaxSequenceRange1000 => 0x33
  | .exceededMaxRetransRequestsInADay => 0x34
  | .exceededMaxRefreshRequestsInADay => 0x35
  | .rejectedRequestedSeqnum1000000PacketsInThePastUseRefreshToRecoverCurrentStateIfNecessary => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReason :=
  if byte = 0x30 then .requestAccepted
  else if byte = 0x31 then .rejectedDueToPermissions
  else if byte = 0x32 then .invalidSequenceRangeEgLowHigh
  else if byte = 0x33 then .exceededMaxSequenceRange1000
  else if byte = 0x34 then .exceededMaxRetransRequestsInADay
  else if byte = 0x35 then .exceededMaxRefreshRequestsInADay
  else .rejectedRequestedSeqnum1000000PacketsInThePastUseRefreshToRecoverCurrentStateIfNecessary

def ofByte (byte : UInt8) : RejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReason) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | rejectedDueToPermissions => decide
  | invalidSequenceRangeEgLowHigh => decide
  | exceededMaxSequenceRange1000 => decide
  | exceededMaxRetransRequestsInADay => decide
  | exceededMaxRefreshRequestsInADay => decide
  | rejectedRequestedSeqnum1000000PacketsInThePastUseRefreshToRecoverCurrentStateIfNecessary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RejectReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RejectReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReason

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x57]

inductive QuoteCondition where
  | noSpecialQuoteCondition -- No Special Quote Condition
  | slowQuote -- Slow Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .noSpecialQuoteCondition => 0x20
  | .slowQuote => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x20 then .noSpecialQuoteCondition
  else .slowQuote

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | noSpecialQuoteCondition => decide
  | slowQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x50, 0x42, 0x45, 0x4F, 0x4C, 0x58, 0x48, 0x36]

inductive TradingStatus where
  | preOpening -- Pre Opening
  | beginAcceptingOrders -- Begin Accepting Orders
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSession -- Late Session
  | closed -- Closed
  | halted -- Halted
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .preOpening => 0x50
  | .beginAcceptingOrders => 0x42
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSession => 0x4C
  | .closed => 0x58
  | .halted => 0x48
  | .suspended => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x50 then .preOpening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSession
  else if byte = 0x58 then .closed
  else if byte = 0x48 then .halted
  else .suspended

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | beginAcceptingOrders => decide
  | earlySession => decide
  | coreSession => decide
  | lateSession => decide
  | closed => decide
  | halted => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Reason Code: one byte code -/
def ReasonCode.codes : List UInt8 :=
  [0x4F, 0x43, 0x45, 0x58]

inductive ReasonCode where
  | newOrderadditionalInterestAdded -- New Orderadditional Interest Added
  | cancel -- Cancel
  | execution -- Execution
  | multipleEvents -- Multiple Events
  | unlisted (byte : { byte : UInt8 // byte ∉ ReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReasonCode

def toByte : ReasonCode → UInt8
  | .newOrderadditionalInterestAdded => 0x4F
  | .cancel => 0x43
  | .execution => 0x45
  | .multipleEvents => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReasonCode :=
  if byte = 0x4F then .newOrderadditionalInterestAdded
  else if byte = 0x43 then .cancel
  else if byte = 0x45 then .execution
  else .multipleEvents

def ofByte (byte : UInt8) : ReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReasonCode) : ofByte value.toByte = value := by
  cases value with
  | newOrderadditionalInterestAdded => decide
  | cancel => decide
  | execution => decide
  | multipleEvents => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReasonCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReasonCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReasonCode

/-- Symbol Index Mapping Response Message: 16 bytes -/
structure SymbolIndexMappingResponseMessage where
  symbol11 : Alpha 11
  filler1 : Alpha 1
  symbolIndex : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolIndexMappingResponseMessage

def encode (message : SymbolIndexMappingResponseMessage) : List UInt8 :=
  Alpha.encode message.symbol11
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 4 message.symbolIndex))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingResponseMessage × List UInt8) := do
  let (symbol11, bytes) ← Alpha.decode 11 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  pure ({ symbol11, filler1, symbolIndex }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingResponseMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SymbolIndexMappingResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SymbolIndexMappingResponseMessage

/-- Symbol Index Mapping Response Messages -/
structure SymbolIndexMappingResponseMessages (messageCount : BitVec 8) where
  symbolIndexMappingResponseMessage : Exact messageCount.toNat SymbolIndexMappingResponseMessage
  deriving DecidableEq, Repr

namespace SymbolIndexMappingResponseMessages

def encode {messageCount : BitVec 8} (message : SymbolIndexMappingResponseMessages messageCount) : List UInt8 :=
  encodeMany SymbolIndexMappingResponseMessage.encode message.symbolIndexMappingResponseMessage.val

def decode (messageCount : BitVec 8) (bytes : List UInt8) : Option (SymbolIndexMappingResponseMessages messageCount × List UInt8) := do
  let (symbolIndexMappingResponseMessage_, bytes) ← decodeMany SymbolIndexMappingResponseMessage.decode messageCount.toNat bytes
  if fits_symbolIndexMappingResponseMessage : symbolIndexMappingResponseMessage_.length = messageCount.toNat then
    pure ({ symbolIndexMappingResponseMessage := ⟨symbolIndexMappingResponseMessage_, fits_symbolIndexMappingResponseMessage⟩ }, bytes)
  else none

@[simp] theorem decode_encode (messageCount : BitVec 8) (message : SymbolIndexMappingResponseMessages messageCount) (rest : List UInt8) :
    decode messageCount (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact messageCount.toNat SymbolIndexMappingResponseMessage.encode SymbolIndexMappingResponseMessage.decode SymbolIndexMappingResponseMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.symbolIndexMappingResponseMessage.length_eq]
  rfl

end SymbolIndexMappingResponseMessages

/-- Sequence Number Reset Message: 4 bytes -/
structure SequenceNumberResetMessage where
  nextSeqNumber : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUInt 4 message.nextSeqNumber

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (nextSeqNumber, bytes) ← decodeUInt 4 bytes
  pure ({ nextSeqNumber }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SequenceNumberResetMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Unavailable Message: 8 bytes -/
structure UnavailableMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace UnavailableMessage

def encode (message : UnavailableMessage) : List UInt8 :=
  encodeUInt 4 message.beginSeqNum
    ++ (encodeUInt 4 message.endSeqNum)

def decode (bytes : List UInt8) : Option (UnavailableMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUInt 4 bytes
  let (endSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : UnavailableMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : UnavailableMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnavailableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnavailableMessage

/-- Request Response Message: 28 bytes -/
structure RequestResponseMessage where
  sourceSeqNum : BitVec 32
  sourceId : Alpha 20
  status : Status
  rejectReason : RejectReason
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace RequestResponseMessage

def encode (message : RequestResponseMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (Alpha.encode message.sourceId
    ++ (Status.encode message.status
    ++ (RejectReason.encode message.rejectReason
    ++ (Alpha.encode message.filler2))))

def decode (bytes : List UInt8) : Option (RequestResponseMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  let (status, bytes) ← Status.decode bytes
  let (rejectReason, bytes) ← RejectReason.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceSeqNum, sourceId, status, rejectReason, filler2 }, bytes)

@[simp] theorem encode_length (message : RequestResponseMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Status.encode_length, RejectReason.encode_length]

theorem encode_length_pos (message : RequestResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RejectReason.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestResponseMessage

/-- Heartbeat Subscription Message: 0 bytes -/
structure HeartbeatSubscriptionMessage where
  deriving DecidableEq, Repr

namespace HeartbeatSubscriptionMessage

def encode (_ : HeartbeatSubscriptionMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatSubscriptionMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatSubscriptionMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatSubscriptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatSubscriptionMessage

/-- Retransmission Request Message: 28 bytes -/
structure RetransmissionRequestMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  sourceId : Alpha 20
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUInt 4 message.beginSeqNum
    ++ (encodeUInt 4 message.endSeqNum
    ++ (Alpha.encode message.sourceId))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUInt 4 bytes
  let (endSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  pure ({ beginSeqNum, endSeqNum, sourceId }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Book Refresh Request Message: 36 bytes -/
structure BookRefreshRequestMessage where
  symbol16 : Alpha 16
  sourceId : Alpha 20
  deriving DecidableEq, Repr

namespace BookRefreshRequestMessage

def encode (message : BookRefreshRequestMessage) : List UInt8 :=
  Alpha.encode message.symbol16
    ++ (Alpha.encode message.sourceId)

def decode (bytes : List UInt8) : Option (BookRefreshRequestMessage × List UInt8) := do
  let (symbol16, bytes) ← Alpha.decode 16 bytes
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol16, sourceId }, bytes)

@[simp] theorem encode_length (message : BookRefreshRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BookRefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookRefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BookRefreshRequestMessage

/-- Heartbeat Response Message: 20 bytes -/
structure HeartbeatResponseMessage where
  sourceId : Alpha 20
  deriving DecidableEq, Repr

namespace HeartbeatResponseMessage

def encode (message : HeartbeatResponseMessage) : List UInt8 :=
  Alpha.encode message.sourceId

def decode (bytes : List UInt8) : Option (HeartbeatResponseMessage × List UInt8) := do
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  pure ({ sourceId }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponseMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponseMessage

/-- Extended Book Refresh Request Message: 26 bytes -/
structure ExtendedBookRefreshRequestMessage where
  sourceId : Alpha 20
  symbolIndex : BitVec 32
  msgType : BitVec 16
  deriving DecidableEq, Repr

namespace ExtendedBookRefreshRequestMessage

def encode (message : ExtendedBookRefreshRequestMessage) : List UInt8 :=
  Alpha.encode message.sourceId
    ++ (encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 2 message.msgType))

def decode (bytes : List UInt8) : Option (ExtendedBookRefreshRequestMessage × List UInt8) := do
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (msgType, bytes) ← decodeUInt 2 bytes
  pure ({ sourceId, symbolIndex, msgType }, bytes)

@[simp] theorem encode_length (message : ExtendedBookRefreshRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExtendedBookRefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExtendedBookRefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExtendedBookRefreshRequestMessage

/-- Symbol Index Mapping Request Message: 24 bytes -/
structure SymbolIndexMappingRequestMessage where
  sourceId : Alpha 20
  symbolIndex : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolIndexMappingRequestMessage

def encode (message : SymbolIndexMappingRequestMessage) : List UInt8 :=
  Alpha.encode message.sourceId
    ++ (encodeUInt 4 message.symbolIndex)

def decode (bytes : List UInt8) : Option (SymbolIndexMappingRequestMessage × List UInt8) := do
  let (sourceId, bytes) ← Alpha.decode 20 bytes
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  pure ({ sourceId, symbolIndex }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SymbolIndexMappingRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SymbolIndexMappingRequestMessage

/-- Full Price Point: 12 bytes -/
structure FullPricePoint where
  priceNumerator : BitVec 32
  volume : BitVec 32
  numOrders : BitVec 16
  side : Side
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace FullPricePoint

def encode (message : FullPricePoint) : List UInt8 :=
  encodeUInt 4 message.priceNumerator
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 2 message.numOrders
    ++ (Side.encode message.side
    ++ (Alpha.encode message.filler1))))

def decode (bytes : List UInt8) : Option (FullPricePoint × List UInt8) := do
  let (priceNumerator, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (numOrders, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ priceNumerator, volume, numOrders, side, filler1 }, bytes)

@[simp] theorem encode_length (message : FullPricePoint) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : FullPricePoint) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullPricePoint) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FullPricePoint

/-- Full Update Message Body -/
structure FullUpdateMessageBody where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  symbolSeqNum : BitVec 32
  sourceSessionId : BitVec 8
  symbol11 : Alpha 11
  priceScaleCode : BitVec 8
  quoteCondition : QuoteCondition
  tradingStatus : TradingStatus
  filler1 : Alpha 1
  mpv : BitVec 16
  fullPricePoint : List FullPricePoint
  deriving DecidableEq, Repr

namespace FullUpdateMessageBody

def encode (message : FullUpdateMessageBody) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 4 message.symbolSeqNum
    ++ (encodeUInt 1 message.sourceSessionId
    ++ (Alpha.encode message.symbol11
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (TradingStatus.encode message.tradingStatus
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.mpv
    ++ (encodeMany FullPricePoint.encode message.fullPricePoint)))))))))))

def decode (bytes : List UInt8) : Option FullUpdateMessageBody := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (symbolSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceSessionId, bytes) ← decodeUInt 1 bytes
  let (symbol11, bytes) ← Alpha.decode 11 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (mpv, bytes) ← decodeUInt 2 bytes
  let fullPricePoint ← decodeAll FullPricePoint.decode bytes.length bytes
  pure { symbolIndex, sourceTime, sourceTimeMicroSecs, symbolSeqNum, sourceSessionId, symbol11, priceScaleCode, quoteCondition, tradingStatus, filler1, mpv, fullPricePoint }

theorem encode_length_pos (message : FullUpdateMessageBody) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : FullUpdateMessageBody) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany FullPricePoint.encode FullPricePoint.decode FullPricePoint.decode_encode FullPricePoint.encode_length_pos message.fullPricePoint _ (encodeMany_length_ge FullPricePoint.encode FullPricePoint.encode_length_pos message.fullPricePoint), some_bind]
  rfl

end FullUpdateMessageBody

/-- Full Update Message: the body with the proof its encoding fits Update Size, whose 2 bytes no bound of the fields fits -/
abbrev FullUpdateMessage := Fitting FullUpdateMessageBody.encode 2 65536

namespace FullUpdateMessage

def encode (message : FullUpdateMessage) : List UInt8 :=
  encodeFramed 2 2 FullUpdateMessageBody.encode message.val

def decode : List UInt8 → Option (FullUpdateMessage × List UInt8) :=
  decodeFittingAll 2 2 FullUpdateMessageBody.encode FullUpdateMessageBody.decode

@[simp] theorem decode_encode (message : FullUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 2 FullUpdateMessageBody.encode FullUpdateMessageBody.decode message (FullUpdateMessageBody.decode_encode message.val) rest

theorem encode_length_pos (message : FullUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : FullUpdateMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end FullUpdateMessage

/-- Full Update Messages -/
structure FullUpdateMessages (messageCount : BitVec 8) where
  fullUpdateMessage : Exact messageCount.toNat FullUpdateMessage
  deriving DecidableEq, Repr

namespace FullUpdateMessages

def encode {messageCount : BitVec 8} (message : FullUpdateMessages messageCount) : List UInt8 :=
  encodeMany FullUpdateMessage.encode message.fullUpdateMessage.val

def decode (messageCount : BitVec 8) (bytes : List UInt8) : Option (FullUpdateMessages messageCount × List UInt8) := do
  let (fullUpdateMessage_, bytes) ← decodeMany FullUpdateMessage.decode messageCount.toNat bytes
  if fits_fullUpdateMessage : fullUpdateMessage_.length = messageCount.toNat then
    pure ({ fullUpdateMessage := ⟨fullUpdateMessage_, fits_fullUpdateMessage⟩ }, bytes)
  else none

@[simp] theorem decode_encode (messageCount : BitVec 8) (message : FullUpdateMessages messageCount) (rest : List UInt8) :
    decode messageCount (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact messageCount.toNat FullUpdateMessage.encode FullUpdateMessage.decode FullUpdateMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fullUpdateMessage.length_eq]
  rfl

end FullUpdateMessages

/-- Delta Price Point: 28 bytes -/
structure DeltaPricePoint where
  priceNumerator : BitVec 32
  volume : BitVec 32
  chgQty : BitVec 32
  numOrders : BitVec 16
  side : Side
  reasonCode : ReasonCode
  linkId1 : BitVec 32
  linkId2 : BitVec 32
  linkId3 : BitVec 32
  deriving DecidableEq, Repr

namespace DeltaPricePoint

def encode (message : DeltaPricePoint) : List UInt8 :=
  encodeUInt 4 message.priceNumerator
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.chgQty
    ++ (encodeUInt 2 message.numOrders
    ++ (Side.encode message.side
    ++ (ReasonCode.encode message.reasonCode
    ++ (encodeUInt 4 message.linkId1
    ++ (encodeUInt 4 message.linkId2
    ++ (encodeUInt 4 message.linkId3))))))))

def decode (bytes : List UInt8) : Option (DeltaPricePoint × List UInt8) := do
  let (priceNumerator, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (chgQty, bytes) ← decodeUInt 4 bytes
  let (numOrders, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (reasonCode, bytes) ← ReasonCode.decode bytes
  let (linkId1, bytes) ← decodeUInt 4 bytes
  let (linkId2, bytes) ← decodeUInt 4 bytes
  let (linkId3, bytes) ← decodeUInt 4 bytes
  pure ({ priceNumerator, volume, chgQty, numOrders, side, reasonCode, linkId1, linkId2, linkId3 }, bytes)

@[simp] theorem encode_length (message : DeltaPricePoint) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, ReasonCode.encode_length]

theorem encode_length_pos (message : DeltaPricePoint) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeltaPricePoint) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReasonCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DeltaPricePoint

/-- Delta Update Message Body -/
structure DeltaUpdateMessageBody where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  sourceSeqNum : BitVec 32
  sourceSessionId : BitVec 8
  quoteCondition : QuoteCondition
  tradingStatus : TradingStatus
  priceScaleCode : BitVec 8
  deltaPricePoint : List DeltaPricePoint
  deriving DecidableEq, Repr

namespace DeltaUpdateMessageBody

def encode (message : DeltaUpdateMessageBody) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 1 message.sourceSessionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeMany DeltaPricePoint.encode message.deltaPricePoint))))))))

def decode (bytes : List UInt8) : Option DeltaUpdateMessageBody := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceSessionId, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let deltaPricePoint ← decodeAll DeltaPricePoint.decode bytes.length bytes
  pure { symbolIndex, sourceTime, sourceTimeMicroSecs, sourceSeqNum, sourceSessionId, quoteCondition, tradingStatus, priceScaleCode, deltaPricePoint }

theorem encode_length_pos (message : DeltaUpdateMessageBody) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : DeltaUpdateMessageBody) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany DeltaPricePoint.encode DeltaPricePoint.decode DeltaPricePoint.decode_encode DeltaPricePoint.encode_length_pos message.deltaPricePoint _ (encodeMany_length_ge DeltaPricePoint.encode DeltaPricePoint.encode_length_pos message.deltaPricePoint), some_bind]
  rfl

end DeltaUpdateMessageBody

/-- Delta Update Message: the body with the proof its encoding fits Delta Size, whose 2 bytes no bound of the fields fits -/
abbrev DeltaUpdateMessage := Fitting DeltaUpdateMessageBody.encode 2 65536

namespace DeltaUpdateMessage

def encode (message : DeltaUpdateMessage) : List UInt8 :=
  encodeFramed 2 2 DeltaUpdateMessageBody.encode message.val

def decode : List UInt8 → Option (DeltaUpdateMessage × List UInt8) :=
  decodeFittingAll 2 2 DeltaUpdateMessageBody.encode DeltaUpdateMessageBody.decode

@[simp] theorem decode_encode (message : DeltaUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 2 DeltaUpdateMessageBody.encode DeltaUpdateMessageBody.decode message (DeltaUpdateMessageBody.decode_encode message.val) rest

theorem encode_length_pos (message : DeltaUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : DeltaUpdateMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end DeltaUpdateMessage

/-- Delta Update Messages -/
structure DeltaUpdateMessages (messageCount : BitVec 8) where
  deltaUpdateMessage : Exact messageCount.toNat DeltaUpdateMessage
  deriving DecidableEq, Repr

namespace DeltaUpdateMessages

def encode {messageCount : BitVec 8} (message : DeltaUpdateMessages messageCount) : List UInt8 :=
  encodeMany DeltaUpdateMessage.encode message.deltaUpdateMessage.val

def decode (messageCount : BitVec 8) (bytes : List UInt8) : Option (DeltaUpdateMessages messageCount × List UInt8) := do
  let (deltaUpdateMessage_, bytes) ← decodeMany DeltaUpdateMessage.decode messageCount.toNat bytes
  if fits_deltaUpdateMessage : deltaUpdateMessage_.length = messageCount.toNat then
    pure ({ deltaUpdateMessage := ⟨deltaUpdateMessage_, fits_deltaUpdateMessage⟩ }, bytes)
  else none

@[simp] theorem decode_encode (messageCount : BitVec 8) (message : DeltaUpdateMessages messageCount) (rest : List UInt8) :
    decode messageCount (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact messageCount.toNat DeltaUpdateMessage.encode DeltaUpdateMessage.decode DeltaUpdateMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.deltaUpdateMessage.length_eq]
  rfl

end DeltaUpdateMessages

/-- Any Payload, selected by Message Type -/
inductive Payload (messageCount : BitVec 8) where
  | symbolIndexMappingResponseMessages (message : SymbolIndexMappingResponseMessages messageCount) -- 35
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | heartbeatMessage (message : HeartbeatMessage) -- 2
  | unavailableMessage (message : UnavailableMessage) -- 5
  | requestResponseMessage (message : RequestResponseMessage) -- 10
  | heartbeatSubscriptionMessage (message : HeartbeatSubscriptionMessage) -- 19
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 20
  | bookRefreshRequestMessage (message : BookRefreshRequestMessage) -- 22
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 24
  | extendedBookRefreshRequestMessage (message : ExtendedBookRefreshRequestMessage) -- 27
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 34
  | fullUpdateMessages (message : FullUpdateMessages messageCount) -- 230
  | deltaUpdateMessages (message : DeltaUpdateMessages messageCount) -- 231
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag {messageCount : BitVec 8} : Payload messageCount → BitVec 16
  | .symbolIndexMappingResponseMessages _ => 35
  | .sequenceNumberResetMessage _ => 1
  | .heartbeatMessage _ => 2
  | .unavailableMessage _ => 5
  | .requestResponseMessage _ => 10
  | .heartbeatSubscriptionMessage _ => 19
  | .retransmissionRequestMessage _ => 20
  | .bookRefreshRequestMessage _ => 22
  | .heartbeatResponseMessage _ => 24
  | .extendedBookRefreshRequestMessage _ => 27
  | .symbolIndexMappingRequestMessage _ => 34
  | .fullUpdateMessages _ => 230
  | .deltaUpdateMessages _ => 231

def encode {messageCount : BitVec 8} : Payload messageCount → List UInt8
  | .symbolIndexMappingResponseMessages message => SymbolIndexMappingResponseMessages.encode message
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .unavailableMessage message => UnavailableMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatSubscriptionMessage message => HeartbeatSubscriptionMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .bookRefreshRequestMessage message => BookRefreshRequestMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .extendedBookRefreshRequestMessage message => ExtendedBookRefreshRequestMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .fullUpdateMessages message => FullUpdateMessages.encode message
  | .deltaUpdateMessages message => DeltaUpdateMessages.encode message

def decode (messageCount : BitVec 8) (tag : BitVec 16) (bytes : List UInt8) : Option (Payload messageCount × List UInt8) :=
  if tag = 35 then (SymbolIndexMappingResponseMessages.decode messageCount bytes).map fun (message, rest) => (.symbolIndexMappingResponseMessages message, rest)
  else if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 5 then (UnavailableMessage.decode bytes).map fun (message, rest) => (.unavailableMessage message, rest)
  else if tag = 10 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 19 then (HeartbeatSubscriptionMessage.decode bytes).map fun (message, rest) => (.heartbeatSubscriptionMessage message, rest)
  else if tag = 20 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 22 then (BookRefreshRequestMessage.decode bytes).map fun (message, rest) => (.bookRefreshRequestMessage message, rest)
  else if tag = 24 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 27 then (ExtendedBookRefreshRequestMessage.decode bytes).map fun (message, rest) => (.extendedBookRefreshRequestMessage message, rest)
  else if tag = 34 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 230 then (FullUpdateMessages.decode messageCount bytes).map fun (message, rest) => (.fullUpdateMessages message, rest)
  else if tag = 231 then (DeltaUpdateMessages.decode messageCount bytes).map fun (message, rest) => (.deltaUpdateMessages message, rest)
  else none

@[simp] theorem decode_encode (messageCount : BitVec 8) (message : Payload messageCount) (rest : List UInt8) :
    decode messageCount (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  sequenceNumber : BitVec 32
  timestamp : BitVec 32
  productId : BitVec 8
  retransmissionFlag : BitVec 8
  messageCount : BitVec 8
  linkFlag : BitVec 8
  payload : Payload messageCount
  deriving DecidableEq, Repr

namespace Packet

def encodeBody (message : Packet) : List UInt8 :=
  encodeUInt 2 (Payload.tag message.payload)
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 4 message.timestamp
    ++ (encodeUInt 1 message.productId
    ++ (encodeUInt 1 message.retransmissionFlag
    ++ (encodeUInt 1 message.messageCount
    ++ (encodeUInt 1 message.linkFlag
    ++ (Payload.encode message.payload)))))))

def decodeBody (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (productId, bytes) ← decodeUInt 1 bytes
  let (retransmissionFlag, bytes) ← decodeUInt 1 bytes
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (linkFlag, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageCount messageType bytes
  pure ({ sequenceNumber, timestamp, productId, retransmissionFlag, messageCount, linkFlag, payload }, bytes)

theorem decodeBody_encodeBody (message : Packet) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Size counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Packet

end Omi.NyseNyseequitiesOpenbookUltraV21K
