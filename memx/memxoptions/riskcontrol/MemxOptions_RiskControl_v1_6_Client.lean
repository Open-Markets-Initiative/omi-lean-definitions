import Wire

/-!
# The Members Exchange Risk Control v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsRiskcontrolSbeV16Client

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
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

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Login Request Message: 2 bytes -/
structure LoginRequestMessage where
  tokenType : Alpha 1
  token : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.tokenType
    ++ (Alpha.encode message.token)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (tokenType, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenType, token }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 20 bytes -/
structure ReplayRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  pure ({ sessionId, nextSequenceNumber, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay All Request Message: 8 bytes -/
structure ReplayAllRequestMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayAllRequestMessage

def encode (message : ReplayAllRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (ReplayAllRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : ReplayAllRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayAllRequestMessage

/-- Stream Request Message: 16 bytes -/
structure StreamRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamRequestMessage

def encode (message : StreamRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamRequestMessage

/-- Risk Settings Query Message: 20 bytes -/
structure RiskSettingsQueryMessage where
  clordid : Alpha 20
  deriving DecidableEq, Repr

namespace RiskSettingsQueryMessage

def encode (message : RiskSettingsQueryMessage) : List UInt8 :=
  Alpha.encode message.clordid

def decode (bytes : List UInt8) : Option (RiskSettingsQueryMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  pure ({ clordid }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RiskSettingsQueryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RiskSettingsQueryMessage

/-- Active Risk Threshold Change Req Message: 34 bytes -/
structure ActiveRiskThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  thresholdQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdChangeReqMessage

def encode (message : ActiveRiskThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 4 message.thresholdQuantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, thresholdQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdChangeReqMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdChangeReqMessage

/-- Active Risk Acknowledgement Req Message: 34 bytes -/
structure ActiveRiskAcknowledgementReqMessage where
  clordid : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgementReqMessage

def encode (message : ActiveRiskAcknowledgementReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.quantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgementReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlier, efid, quantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgementReqMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgementReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgementReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgementReqMessage

/-- Cp Volume Threshold Change Req Message: 44 bytes -/
structure CpVolumeThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  volume : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpVolumeThresholdChangeReqMessage

def encode (message : CpVolumeThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpVolumeThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, volume, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpVolumeThresholdChangeReqMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpVolumeThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpVolumeThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpVolumeThresholdChangeReqMessage

/-- Cp Executed Notional Threshold Change Req Message: 44 bytes -/
structure CpExecutedNotionalThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpExecutedNotionalThresholdChangeReqMessage

def encode (message : CpExecutedNotionalThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpExecutedNotionalThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, priceInDollars, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpExecutedNotionalThresholdChangeReqMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpExecutedNotionalThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpExecutedNotionalThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpExecutedNotionalThresholdChangeReqMessage

/-- Cp Total Executions Threshold Change Req Message: 40 bytes -/
structure CpTotalExecutionsThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  totalExecutions : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpTotalExecutionsThresholdChangeReqMessage

def encode (message : CpTotalExecutionsThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.totalExecutions
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpTotalExecutionsThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (totalExecutions, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, totalExecutions, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpTotalExecutionsThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpTotalExecutionsThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpTotalExecutionsThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpTotalExecutionsThresholdChangeReqMessage

/-- Cp Percent Outstanding Contracts Threshold Change Req Message: 38 bytes -/
structure CpPercentOutstandingContractsThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  percent : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpPercentOutstandingContractsThresholdChangeReqMessage

def encode (message : CpPercentOutstandingContractsThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 4 message.percent
    ++ (encodeUInt 4 message.periodInMilliSeconds))))

def decode (bytes : List UInt8) : Option (CpPercentOutstandingContractsThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (percent, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, percent, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpPercentOutstandingContractsThresholdChangeReqMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpPercentOutstandingContractsThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpPercentOutstandingContractsThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpPercentOutstandingContractsThresholdChangeReqMessage

/-- Cp Breach Count Threshold Change Req Message: 40 bytes -/
structure CpBreachCountThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  count : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpBreachCountThresholdChangeReqMessage

def encode (message : CpBreachCountThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.count
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpBreachCountThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, count, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpBreachCountThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpBreachCountThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpBreachCountThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpBreachCountThresholdChangeReqMessage

/-- Manual Cp Breach Trigger Req Message: 33 bytes -/
structure ManualCpBreachTriggerReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  sendCancels : BitVec 8
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerReqMessage

def encode (message : ManualCpBreachTriggerReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.sendCancels))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (sendCancels, bytes) ← decodeUInt 1 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, sendCancels }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerReqMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerReqMessage

/-- Cp Clear Breach Req Message: 28 bytes -/
structure CpClearBreachReqMessage where
  clordid : Alpha 20
  breachIdOptional : BitVec 64
  deriving DecidableEq, Repr

namespace CpClearBreachReqMessage

def encode (message : CpClearBreachReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 8 message.breachIdOptional)

def decode (bytes : List UInt8) : Option (CpClearBreachReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, breachIdOptional }, bytes)

@[simp] theorem encode_length (message : CpClearBreachReqMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpClearBreachReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearBreachReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpClearBreachReqMessage

/-- Single Order Allow Iso Orders Change Req Message: 33 bytes -/
structure SingleOrderAllowIsoOrdersChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowIsoOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowIsoOrdersChangeReqMessage

def encode (message : SingleOrderAllowIsoOrdersChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowIsoOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowIsoOrdersChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowIsoOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, allowIsoOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowIsoOrdersChangeReqMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowIsoOrdersChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowIsoOrdersChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowIsoOrdersChangeReqMessage

/-- Single Order Allow Orders In Crossed Market Change Req Message: 33 bytes -/
structure SingleOrderAllowOrdersInCrossedMarketChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowOrdersInCrossedMarketChangeReqMessage

def encode (message : SingleOrderAllowOrdersInCrossedMarketChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowOrdersInCrossedMarketChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, allowOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowOrdersInCrossedMarketChangeReqMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowOrdersInCrossedMarketChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowOrdersInCrossedMarketChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowOrdersInCrossedMarketChangeReqMessage

/-- Single Order Max Notional Change Req Message: 40 bytes -/
structure SingleOrderMaxNotionalChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxNotionalInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace SingleOrderMaxNotionalChangeReqMessage

def encode (message : SingleOrderMaxNotionalChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.maxNotionalInDollars))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxNotionalChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxNotionalInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, maxNotionalInDollars }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxNotionalChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxNotionalChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxNotionalChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxNotionalChangeReqMessage

/-- Single Order Max Contracts Change Req Message: 36 bytes -/
structure SingleOrderMaxContractsChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleOrderMaxContractsChangeReqMessage

def encode (message : SingleOrderMaxContractsChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxContracts))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxContractsChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxContracts, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, maxContracts }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxContractsChangeReqMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxContractsChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxContractsChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxContractsChangeReqMessage

/-- Cp Gross Notional Threshold Change Req Message: 40 bytes -/
structure CpGrossNotionalThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpGrossNotionalThresholdChangeReqMessage

def encode (message : CpGrossNotionalThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpGrossNotionalThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpGrossNotionalThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpGrossNotionalThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpGrossNotionalThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpGrossNotionalThresholdChangeReqMessage

/-- Cp Market Order Gross Notional Threshold Change Req Message: 40 bytes -/
structure CpMarketOrderGrossNotionalThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderGrossNotionalThresholdChangeReqMessage

def encode (message : CpMarketOrderGrossNotionalThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderGrossNotionalThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderGrossNotionalThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderGrossNotionalThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderGrossNotionalThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderGrossNotionalThresholdChangeReqMessage

/-- Cp Net Notional Threshold Change Req Message: 40 bytes -/
structure CpNetNotionalThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpNetNotionalThresholdChangeReqMessage

def encode (message : CpNetNotionalThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpNetNotionalThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpNetNotionalThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpNetNotionalThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpNetNotionalThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpNetNotionalThresholdChangeReqMessage

/-- Cp Market Order Net Notional Threshold Change Req Message: 40 bytes -/
structure CpMarketOrderNetNotionalThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderNetNotionalThresholdChangeReqMessage

def encode (message : CpMarketOrderNetNotionalThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderNetNotionalThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderNetNotionalThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderNetNotionalThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderNetNotionalThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderNetNotionalThresholdChangeReqMessage

/-- Cp Duplicate Order Threshold Change Req Message: 41 bytes -/
structure CpDuplicateOrderThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxDupOrders : BitVec 32
  useOrderPriceInDupCheckOptional : BitVec 8
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpDuplicateOrderThresholdChangeReqMessage

def encode (message : CpDuplicateOrderThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxDupOrders
    ++ (encodeUInt 1 message.useOrderPriceInDupCheckOptional
    ++ (encodeUInt 4 message.periodInMilliSeconds))))))

def decode (bytes : List UInt8) : Option (CpDuplicateOrderThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxDupOrders, bytes) ← decodeUInt 4 bytes
  let (useOrderPriceInDupCheckOptional, bytes) ← decodeUInt 1 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, maxDupOrders, useOrderPriceInDupCheckOptional, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpDuplicateOrderThresholdChangeReqMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpDuplicateOrderThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpDuplicateOrderThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpDuplicateOrderThresholdChangeReqMessage

/-- Cp Order Rate Threshold Change Req Message: 40 bytes -/
structure CpOrderRateThresholdChangeReqMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxOrderMsgs : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpOrderRateThresholdChangeReqMessage

def encode (message : CpOrderRateThresholdChangeReqMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxOrderMsgs
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpOrderRateThresholdChangeReqMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxOrderMsgs, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, maxOrderMsgs, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpOrderRateThresholdChangeReqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpOrderRateThresholdChangeReqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpOrderRateThresholdChangeReqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpOrderRateThresholdChangeReqMessage

/-- Active Risk Threshold State Message: 38 bytes -/
structure ActiveRiskThresholdStateMessage where
  clordidOptional : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  thresholdQuantity : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdStateMessage

def encode (message : ActiveRiskThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 4 message.unackedQuantity))))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlier, efid, thresholdQuantity, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdStateMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdStateMessage

/-- Active Risk Threshold Change Rej Message: 36 bytes -/
structure ActiveRiskThresholdChangeRejMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  thresholdQuantity : BitVec 32
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdChangeRejMessage

def encode (message : ActiveRiskThresholdChangeRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdChangeRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, underlierOptional, efidOptional, thresholdQuantity, rejectReason }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdChangeRejMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdChangeRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdChangeRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskThresholdChangeRejMessage

/-- Active Risk Acknowledged Message: 38 bytes -/
structure ActiveRiskAcknowledgedMessage where
  clordid : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  quantity : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgedMessage

def encode (message : ActiveRiskAcknowledgedMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.unackedQuantity))))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgedMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlier, efid, quantity, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgedMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgedMessage

/-- Active Risk Acknowledge Rej Message: 36 bytes -/
structure ActiveRiskAcknowledgeRejMessage where
  clordid : Alpha 20
  underlier : Alpha 6
  efid : Alpha 4
  thresholdQuantity : BitVec 32
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgeRejMessage

def encode (message : ActiveRiskAcknowledgeRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.efid
    ++ (encodeUInt 4 message.thresholdQuantity
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgeRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, underlier, efid, thresholdQuantity, rejectReason }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgeRejMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgeRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgeRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskAcknowledgeRejMessage

/-- Active Risk Quantity Update Notification Message: 67 bytes -/
structure ActiveRiskQuantityUpdateNotificationMessage where
  sendingTime : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  trdMatchId : BitVec 64
  efid : Alpha 4
  underlier : Alpha 6
  optionSecurityId : Alpha 8
  side : Side
  lastPx : BitVec 64
  lastQty : BitVec 32
  unackedQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskQuantityUpdateNotificationMessage

def encode (message : ActiveRiskQuantityUpdateNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.trdMatchId
    ++ (Alpha.encode message.efid
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.optionSecurityId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 4 message.unackedQuantity))))))))))

def decode (bytes : List UInt8) : Option (ActiveRiskQuantityUpdateNotificationMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (efid, bytes) ← Alpha.decode 4 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (optionSecurityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (unackedQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ sendingTime, transactTime, orderId, trdMatchId, efid, underlier, optionSecurityId, side, lastPx, lastQty, unackedQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskQuantityUpdateNotificationMessage) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : ActiveRiskQuantityUpdateNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskQuantityUpdateNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveRiskQuantityUpdateNotificationMessage

/-- Cp Volume Threshold State Message: 44 bytes -/
structure CpVolumeThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  volume : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpVolumeThresholdStateMessage

def encode (message : CpVolumeThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpVolumeThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, volume, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpVolumeThresholdStateMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpVolumeThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpVolumeThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpVolumeThresholdStateMessage

/-- Cp Executed Notional Threshold State Message: 44 bytes -/
structure CpExecutedNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpExecutedNotionalThresholdStateMessage

def encode (message : CpExecutedNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpExecutedNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpExecutedNotionalThresholdStateMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpExecutedNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpExecutedNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpExecutedNotionalThresholdStateMessage

/-- Cp Total Executions Threshold State Message: 40 bytes -/
structure CpTotalExecutionsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  totalExecutions : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpTotalExecutionsThresholdStateMessage

def encode (message : CpTotalExecutionsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.totalExecutions
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpTotalExecutionsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (totalExecutions, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, totalExecutions, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpTotalExecutionsThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpTotalExecutionsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpTotalExecutionsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpTotalExecutionsThresholdStateMessage

/-- Cp Percent Outstanding Contracts Threshold State Message: 38 bytes -/
structure CpPercentOutstandingContractsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  percent : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpPercentOutstandingContractsThresholdStateMessage

def encode (message : CpPercentOutstandingContractsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 4 message.percent
    ++ (encodeUInt 4 message.periodInMilliSeconds))))

def decode (bytes : List UInt8) : Option (CpPercentOutstandingContractsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (percent, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, percent, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpPercentOutstandingContractsThresholdStateMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpPercentOutstandingContractsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpPercentOutstandingContractsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpPercentOutstandingContractsThresholdStateMessage

/-- Cp Breach Count Threshold State Message: 40 bytes -/
structure CpBreachCountThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  count : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpBreachCountThresholdStateMessage

def encode (message : CpBreachCountThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.count
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpBreachCountThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, count, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpBreachCountThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpBreachCountThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpBreachCountThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpBreachCountThresholdStateMessage

/-- Manual Cp Breach Trigger Pending Message: 40 bytes -/
structure ManualCpBreachTriggerPendingMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  breachId : BitVec 64
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerPendingMessage

def encode (message : ManualCpBreachTriggerPendingMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.breachId))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerPendingMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (breachId, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, breachId }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerPendingMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerPendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerPendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerPendingMessage

/-- Manual Cp Breach Trigger Done Message: 44 bytes -/
structure ManualCpBreachTriggerDoneMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  breachId : BitVec 64
  totalAffectedOrders : BitVec 32
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerDoneMessage

def encode (message : ManualCpBreachTriggerDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.breachId
    ++ (encodeUInt 4 message.totalAffectedOrders)))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (breachId, bytes) ← decodeUInt 8 bytes
  let (totalAffectedOrders, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, breachId, totalAffectedOrders }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerDoneMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerDoneMessage

/-- Risk Threshold Update Rej Message: 23 bytes -/
structure RiskThresholdUpdateRejMessage where
  clordid : Alpha 20
  riskType : BitVec 8
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace RiskThresholdUpdateRejMessage

def encode (message : RiskThresholdUpdateRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 1 message.riskType
    ++ (encodeUInt 2 message.rejectReason))

def decode (bytes : List UInt8) : Option (RiskThresholdUpdateRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (riskType, bytes) ← decodeUInt 1 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, riskType, rejectReason }, bytes)

@[simp] theorem encode_length (message : RiskThresholdUpdateRejMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskThresholdUpdateRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskThresholdUpdateRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskThresholdUpdateRejMessage

/-- Passive Risk Threshold Notification Message: 30 bytes -/
structure PassiveRiskThresholdNotificationMessage where
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  ruleType : BitVec 8
  latestPercentage : BitVec 8
  breachIdOptional : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PassiveRiskThresholdNotificationMessage

def encode (message : PassiveRiskThresholdNotificationMessage) : List UInt8 :=
  Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.ruleType
    ++ (encodeUInt 1 message.latestPercentage
    ++ (encodeUInt 8 message.breachIdOptional
    ++ (encodeUInt 8 message.transactTime))))))

def decode (bytes : List UInt8) : Option (PassiveRiskThresholdNotificationMessage × List UInt8) := do
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (ruleType, bytes) ← decodeUInt 1 bytes
  let (latestPercentage, bytes) ← decodeUInt 1 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ underlierOptional, efidOptional, riskGroupId, ruleType, latestPercentage, breachIdOptional, transactTime }, bytes)

@[simp] theorem encode_length (message : PassiveRiskThresholdNotificationMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PassiveRiskThresholdNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PassiveRiskThresholdNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PassiveRiskThresholdNotificationMessage

/-- Single Order Allow Iso Orders State Message: 33 bytes -/
structure SingleOrderAllowIsoOrdersStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowIsoOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowIsoOrdersStateMessage

def encode (message : SingleOrderAllowIsoOrdersStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowIsoOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowIsoOrdersStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowIsoOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, allowIsoOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowIsoOrdersStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowIsoOrdersStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowIsoOrdersStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowIsoOrdersStateMessage

/-- Single Order Allow Orders In Crossed Market State Message: 33 bytes -/
structure SingleOrderAllowOrdersInCrossedMarketStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowOrdersInCrossedMarketStateMessage

def encode (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowOrdersInCrossedMarketStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, allowOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderAllowOrdersInCrossedMarketStateMessage

/-- Single Order Max Notional Threshold State Message: 40 bytes -/
structure SingleOrderMaxNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxNotionalInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace SingleOrderMaxNotionalThresholdStateMessage

def encode (message : SingleOrderMaxNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.maxNotionalInDollars))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxNotionalInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxNotionalInDollars }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxNotionalThresholdStateMessage

/-- Single Order Max Contracts Threshold State Message: 36 bytes -/
structure SingleOrderMaxContractsThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleOrderMaxContractsThresholdStateMessage

def encode (message : SingleOrderMaxContractsThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxContracts))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxContractsThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxContracts, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxContracts }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxContractsThresholdStateMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxContractsThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxContractsThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleOrderMaxContractsThresholdStateMessage

/-- Risk Settings Query Done Message: 24 bytes -/
structure RiskSettingsQueryDoneMessage where
  clordid : Alpha 20
  numberMsgsSent : BitVec 32
  deriving DecidableEq, Repr

namespace RiskSettingsQueryDoneMessage

def encode (message : RiskSettingsQueryDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 4 message.numberMsgsSent)

def decode (bytes : List UInt8) : Option (RiskSettingsQueryDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (numberMsgsSent, bytes) ← decodeUInt 4 bytes
  pure ({ clordid, numberMsgsSent }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryDoneMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskSettingsQueryDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskSettingsQueryDoneMessage

/-- Risk Settings Query Rej Message: 22 bytes -/
structure RiskSettingsQueryRejMessage where
  clordid : Alpha 20
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace RiskSettingsQueryRejMessage

def encode (message : RiskSettingsQueryRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 2 message.rejectReason)

def decode (bytes : List UInt8) : Option (RiskSettingsQueryRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, rejectReason }, bytes)

@[simp] theorem encode_length (message : RiskSettingsQueryRejMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskSettingsQueryRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskSettingsQueryRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RiskSettingsQueryRejMessage

/-- Manual Cp Breach Trigger Rej Message: 34 bytes -/
structure ManualCpBreachTriggerRejMessage where
  clordid : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerRejMessage

def encode (message : ManualCpBreachTriggerRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 2 message.rejectReason))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, underlierOptional, efidOptional, riskGroupId, rejectReason }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerRejMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ManualCpBreachTriggerRejMessage

/-- Breach Clear Rej Message: 30 bytes -/
structure BreachClearRejMessage where
  clordid : Alpha 20
  breachIdOptional : BitVec 64
  rejectReason : BitVec 16
  deriving DecidableEq, Repr

namespace BreachClearRejMessage

def encode (message : BreachClearRejMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 8 message.breachIdOptional
    ++ (encodeUInt 2 message.rejectReason))

def decode (bytes : List UInt8) : Option (BreachClearRejMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  let (rejectReason, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, breachIdOptional, rejectReason }, bytes)

@[simp] theorem encode_length (message : BreachClearRejMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearRejMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearRejMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearRejMessage

/-- Breach Cleared Message: 28 bytes -/
structure BreachClearedMessage where
  clordidOptional : Alpha 20
  breachIdOptional : BitVec 64
  deriving DecidableEq, Repr

namespace BreachClearedMessage

def encode (message : BreachClearedMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (encodeUInt 8 message.breachIdOptional)

def decode (bytes : List UInt8) : Option (BreachClearedMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (breachIdOptional, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, breachIdOptional }, bytes)

@[simp] theorem encode_length (message : BreachClearedMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BreachClearedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreachClearedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BreachClearedMessage

/-- Cp Gross Notional Threshold State Message: 40 bytes -/
structure CpGrossNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpGrossNotionalThresholdStateMessage

def encode (message : CpGrossNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpGrossNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpGrossNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpGrossNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpGrossNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpGrossNotionalThresholdStateMessage

/-- Cp Market Order Gross Notional Threshold State Message: 40 bytes -/
structure CpMarketOrderGrossNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderGrossNotionalThresholdStateMessage

def encode (message : CpMarketOrderGrossNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderGrossNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderGrossNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderGrossNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderGrossNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderGrossNotionalThresholdStateMessage

/-- Cp Net Notional Threshold State Message: 40 bytes -/
structure CpNetNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpNetNotionalThresholdStateMessage

def encode (message : CpNetNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpNetNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpNetNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpNetNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpNetNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpNetNotionalThresholdStateMessage

/-- Cp Market Order Net Notional Threshold State Message: 40 bytes -/
structure CpMarketOrderNetNotionalThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderNetNotionalThresholdStateMessage

def encode (message : CpMarketOrderNetNotionalThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderNetNotionalThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderNetNotionalThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderNetNotionalThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderNetNotionalThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpMarketOrderNetNotionalThresholdStateMessage

/-- Cp Duplicate Order Threshold State Message: 41 bytes -/
structure CpDuplicateOrderThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxDupOrders : BitVec 32
  useOrderPriceInDupCheck : BitVec 8
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpDuplicateOrderThresholdStateMessage

def encode (message : CpDuplicateOrderThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxDupOrders
    ++ (encodeUInt 1 message.useOrderPriceInDupCheck
    ++ (encodeUInt 4 message.periodInMilliSeconds))))))

def decode (bytes : List UInt8) : Option (CpDuplicateOrderThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxDupOrders, bytes) ← decodeUInt 4 bytes
  let (useOrderPriceInDupCheck, bytes) ← decodeUInt 1 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxDupOrders, useOrderPriceInDupCheck, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpDuplicateOrderThresholdStateMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpDuplicateOrderThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpDuplicateOrderThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpDuplicateOrderThresholdStateMessage

/-- Cp Order Rate Threshold State Message: 40 bytes -/
structure CpOrderRateThresholdStateMessage where
  clordidOptional : Alpha 20
  underlierOptional : Alpha 6
  efidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxOrderMsgs : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpOrderRateThresholdStateMessage

def encode (message : CpOrderRateThresholdStateMessage) : List UInt8 :=
  Alpha.encode message.clordidOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxOrderMsgs
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpOrderRateThresholdStateMessage × List UInt8) := do
  let (clordidOptional, bytes) ← Alpha.decode 20 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxOrderMsgs, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clordidOptional, underlierOptional, efidOptional, riskGroupId, maxOrderMsgs, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpOrderRateThresholdStateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpOrderRateThresholdStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpOrderRateThresholdStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpOrderRateThresholdStateMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | riskSettingsQueryMessage (message : RiskSettingsQueryMessage) -- 1
  | activeRiskThresholdChangeReqMessage (message : ActiveRiskThresholdChangeReqMessage) -- 2
  | activeRiskAcknowledgementReqMessage (message : ActiveRiskAcknowledgementReqMessage) -- 3
  | cpVolumeThresholdChangeReqMessage (message : CpVolumeThresholdChangeReqMessage) -- 4
  | cpExecutedNotionalThresholdChangeReqMessage (message : CpExecutedNotionalThresholdChangeReqMessage) -- 5
  | cpTotalExecutionsThresholdChangeReqMessage (message : CpTotalExecutionsThresholdChangeReqMessage) -- 6
  | cpPercentOutstandingContractsThresholdChangeReqMessage (message : CpPercentOutstandingContractsThresholdChangeReqMessage) -- 7
  | cpBreachCountThresholdChangeReqMessage (message : CpBreachCountThresholdChangeReqMessage) -- 8
  | manualCpBreachTriggerReqMessage (message : ManualCpBreachTriggerReqMessage) -- 9
  | cpClearBreachReqMessage (message : CpClearBreachReqMessage) -- 10
  | singleOrderAllowIsoOrdersChangeReqMessage (message : SingleOrderAllowIsoOrdersChangeReqMessage) -- 11
  | singleOrderAllowOrdersInCrossedMarketChangeReqMessage (message : SingleOrderAllowOrdersInCrossedMarketChangeReqMessage) -- 12
  | singleOrderMaxNotionalChangeReqMessage (message : SingleOrderMaxNotionalChangeReqMessage) -- 13
  | singleOrderMaxContractsChangeReqMessage (message : SingleOrderMaxContractsChangeReqMessage) -- 14
  | cpGrossNotionalThresholdChangeReqMessage (message : CpGrossNotionalThresholdChangeReqMessage) -- 18
  | cpMarketOrderGrossNotionalThresholdChangeReqMessage (message : CpMarketOrderGrossNotionalThresholdChangeReqMessage) -- 19
  | cpNetNotionalThresholdChangeReqMessage (message : CpNetNotionalThresholdChangeReqMessage) -- 20
  | cpMarketOrderNetNotionalThresholdChangeReqMessage (message : CpMarketOrderNetNotionalThresholdChangeReqMessage) -- 21
  | cpDuplicateOrderThresholdChangeReqMessage (message : CpDuplicateOrderThresholdChangeReqMessage) -- 22
  | cpOrderRateThresholdChangeReqMessage (message : CpOrderRateThresholdChangeReqMessage) -- 23
  | activeRiskThresholdStateMessage (message : ActiveRiskThresholdStateMessage) -- 30
  | activeRiskThresholdChangeRejMessage (message : ActiveRiskThresholdChangeRejMessage) -- 31
  | activeRiskAcknowledgedMessage (message : ActiveRiskAcknowledgedMessage) -- 32
  | activeRiskAcknowledgeRejMessage (message : ActiveRiskAcknowledgeRejMessage) -- 33
  | activeRiskQuantityUpdateNotificationMessage (message : ActiveRiskQuantityUpdateNotificationMessage) -- 34
  | cpVolumeThresholdStateMessage (message : CpVolumeThresholdStateMessage) -- 35
  | cpExecutedNotionalThresholdStateMessage (message : CpExecutedNotionalThresholdStateMessage) -- 36
  | cpTotalExecutionsThresholdStateMessage (message : CpTotalExecutionsThresholdStateMessage) -- 37
  | cpPercentOutstandingContractsThresholdStateMessage (message : CpPercentOutstandingContractsThresholdStateMessage) -- 38
  | cpBreachCountThresholdStateMessage (message : CpBreachCountThresholdStateMessage) -- 39
  | manualCpBreachTriggerPendingMessage (message : ManualCpBreachTriggerPendingMessage) -- 40
  | manualCpBreachTriggerDoneMessage (message : ManualCpBreachTriggerDoneMessage) -- 41
  | riskThresholdUpdateRejMessage (message : RiskThresholdUpdateRejMessage) -- 42
  | passiveRiskThresholdNotificationMessage (message : PassiveRiskThresholdNotificationMessage) -- 43
  | singleOrderAllowIsoOrdersStateMessage (message : SingleOrderAllowIsoOrdersStateMessage) -- 44
  | singleOrderAllowOrdersInCrossedMarketStateMessage (message : SingleOrderAllowOrdersInCrossedMarketStateMessage) -- 45
  | singleOrderMaxNotionalThresholdStateMessage (message : SingleOrderMaxNotionalThresholdStateMessage) -- 46
  | singleOrderMaxContractsThresholdStateMessage (message : SingleOrderMaxContractsThresholdStateMessage) -- 47
  | riskSettingsQueryDoneMessage (message : RiskSettingsQueryDoneMessage) -- 48
  | riskSettingsQueryRejMessage (message : RiskSettingsQueryRejMessage) -- 49
  | manualCpBreachTriggerRejMessage (message : ManualCpBreachTriggerRejMessage) -- 50
  | breachClearRejMessage (message : BreachClearRejMessage) -- 51
  | breachClearedMessage (message : BreachClearedMessage) -- 52
  | cpGrossNotionalThresholdStateMessage (message : CpGrossNotionalThresholdStateMessage) -- 60
  | cpMarketOrderGrossNotionalThresholdStateMessage (message : CpMarketOrderGrossNotionalThresholdStateMessage) -- 61
  | cpNetNotionalThresholdStateMessage (message : CpNetNotionalThresholdStateMessage) -- 62
  | cpMarketOrderNetNotionalThresholdStateMessage (message : CpMarketOrderNetNotionalThresholdStateMessage) -- 63
  | cpDuplicateOrderThresholdStateMessage (message : CpDuplicateOrderThresholdStateMessage) -- 64
  | cpOrderRateThresholdStateMessage (message : CpOrderRateThresholdStateMessage) -- 65
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .riskSettingsQueryMessage _ => 1
  | .activeRiskThresholdChangeReqMessage _ => 2
  | .activeRiskAcknowledgementReqMessage _ => 3
  | .cpVolumeThresholdChangeReqMessage _ => 4
  | .cpExecutedNotionalThresholdChangeReqMessage _ => 5
  | .cpTotalExecutionsThresholdChangeReqMessage _ => 6
  | .cpPercentOutstandingContractsThresholdChangeReqMessage _ => 7
  | .cpBreachCountThresholdChangeReqMessage _ => 8
  | .manualCpBreachTriggerReqMessage _ => 9
  | .cpClearBreachReqMessage _ => 10
  | .singleOrderAllowIsoOrdersChangeReqMessage _ => 11
  | .singleOrderAllowOrdersInCrossedMarketChangeReqMessage _ => 12
  | .singleOrderMaxNotionalChangeReqMessage _ => 13
  | .singleOrderMaxContractsChangeReqMessage _ => 14
  | .cpGrossNotionalThresholdChangeReqMessage _ => 18
  | .cpMarketOrderGrossNotionalThresholdChangeReqMessage _ => 19
  | .cpNetNotionalThresholdChangeReqMessage _ => 20
  | .cpMarketOrderNetNotionalThresholdChangeReqMessage _ => 21
  | .cpDuplicateOrderThresholdChangeReqMessage _ => 22
  | .cpOrderRateThresholdChangeReqMessage _ => 23
  | .activeRiskThresholdStateMessage _ => 30
  | .activeRiskThresholdChangeRejMessage _ => 31
  | .activeRiskAcknowledgedMessage _ => 32
  | .activeRiskAcknowledgeRejMessage _ => 33
  | .activeRiskQuantityUpdateNotificationMessage _ => 34
  | .cpVolumeThresholdStateMessage _ => 35
  | .cpExecutedNotionalThresholdStateMessage _ => 36
  | .cpTotalExecutionsThresholdStateMessage _ => 37
  | .cpPercentOutstandingContractsThresholdStateMessage _ => 38
  | .cpBreachCountThresholdStateMessage _ => 39
  | .manualCpBreachTriggerPendingMessage _ => 40
  | .manualCpBreachTriggerDoneMessage _ => 41
  | .riskThresholdUpdateRejMessage _ => 42
  | .passiveRiskThresholdNotificationMessage _ => 43
  | .singleOrderAllowIsoOrdersStateMessage _ => 44
  | .singleOrderAllowOrdersInCrossedMarketStateMessage _ => 45
  | .singleOrderMaxNotionalThresholdStateMessage _ => 46
  | .singleOrderMaxContractsThresholdStateMessage _ => 47
  | .riskSettingsQueryDoneMessage _ => 48
  | .riskSettingsQueryRejMessage _ => 49
  | .manualCpBreachTriggerRejMessage _ => 50
  | .breachClearRejMessage _ => 51
  | .breachClearedMessage _ => 52
  | .cpGrossNotionalThresholdStateMessage _ => 60
  | .cpMarketOrderGrossNotionalThresholdStateMessage _ => 61
  | .cpNetNotionalThresholdStateMessage _ => 62
  | .cpMarketOrderNetNotionalThresholdStateMessage _ => 63
  | .cpDuplicateOrderThresholdStateMessage _ => 64
  | .cpOrderRateThresholdStateMessage _ => 65

def encode : Payload → List UInt8
  | .riskSettingsQueryMessage message => RiskSettingsQueryMessage.encode message
  | .activeRiskThresholdChangeReqMessage message => ActiveRiskThresholdChangeReqMessage.encode message
  | .activeRiskAcknowledgementReqMessage message => ActiveRiskAcknowledgementReqMessage.encode message
  | .cpVolumeThresholdChangeReqMessage message => CpVolumeThresholdChangeReqMessage.encode message
  | .cpExecutedNotionalThresholdChangeReqMessage message => CpExecutedNotionalThresholdChangeReqMessage.encode message
  | .cpTotalExecutionsThresholdChangeReqMessage message => CpTotalExecutionsThresholdChangeReqMessage.encode message
  | .cpPercentOutstandingContractsThresholdChangeReqMessage message => CpPercentOutstandingContractsThresholdChangeReqMessage.encode message
  | .cpBreachCountThresholdChangeReqMessage message => CpBreachCountThresholdChangeReqMessage.encode message
  | .manualCpBreachTriggerReqMessage message => ManualCpBreachTriggerReqMessage.encode message
  | .cpClearBreachReqMessage message => CpClearBreachReqMessage.encode message
  | .singleOrderAllowIsoOrdersChangeReqMessage message => SingleOrderAllowIsoOrdersChangeReqMessage.encode message
  | .singleOrderAllowOrdersInCrossedMarketChangeReqMessage message => SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.encode message
  | .singleOrderMaxNotionalChangeReqMessage message => SingleOrderMaxNotionalChangeReqMessage.encode message
  | .singleOrderMaxContractsChangeReqMessage message => SingleOrderMaxContractsChangeReqMessage.encode message
  | .cpGrossNotionalThresholdChangeReqMessage message => CpGrossNotionalThresholdChangeReqMessage.encode message
  | .cpMarketOrderGrossNotionalThresholdChangeReqMessage message => CpMarketOrderGrossNotionalThresholdChangeReqMessage.encode message
  | .cpNetNotionalThresholdChangeReqMessage message => CpNetNotionalThresholdChangeReqMessage.encode message
  | .cpMarketOrderNetNotionalThresholdChangeReqMessage message => CpMarketOrderNetNotionalThresholdChangeReqMessage.encode message
  | .cpDuplicateOrderThresholdChangeReqMessage message => CpDuplicateOrderThresholdChangeReqMessage.encode message
  | .cpOrderRateThresholdChangeReqMessage message => CpOrderRateThresholdChangeReqMessage.encode message
  | .activeRiskThresholdStateMessage message => ActiveRiskThresholdStateMessage.encode message
  | .activeRiskThresholdChangeRejMessage message => ActiveRiskThresholdChangeRejMessage.encode message
  | .activeRiskAcknowledgedMessage message => ActiveRiskAcknowledgedMessage.encode message
  | .activeRiskAcknowledgeRejMessage message => ActiveRiskAcknowledgeRejMessage.encode message
  | .activeRiskQuantityUpdateNotificationMessage message => ActiveRiskQuantityUpdateNotificationMessage.encode message
  | .cpVolumeThresholdStateMessage message => CpVolumeThresholdStateMessage.encode message
  | .cpExecutedNotionalThresholdStateMessage message => CpExecutedNotionalThresholdStateMessage.encode message
  | .cpTotalExecutionsThresholdStateMessage message => CpTotalExecutionsThresholdStateMessage.encode message
  | .cpPercentOutstandingContractsThresholdStateMessage message => CpPercentOutstandingContractsThresholdStateMessage.encode message
  | .cpBreachCountThresholdStateMessage message => CpBreachCountThresholdStateMessage.encode message
  | .manualCpBreachTriggerPendingMessage message => ManualCpBreachTriggerPendingMessage.encode message
  | .manualCpBreachTriggerDoneMessage message => ManualCpBreachTriggerDoneMessage.encode message
  | .riskThresholdUpdateRejMessage message => RiskThresholdUpdateRejMessage.encode message
  | .passiveRiskThresholdNotificationMessage message => PassiveRiskThresholdNotificationMessage.encode message
  | .singleOrderAllowIsoOrdersStateMessage message => SingleOrderAllowIsoOrdersStateMessage.encode message
  | .singleOrderAllowOrdersInCrossedMarketStateMessage message => SingleOrderAllowOrdersInCrossedMarketStateMessage.encode message
  | .singleOrderMaxNotionalThresholdStateMessage message => SingleOrderMaxNotionalThresholdStateMessage.encode message
  | .singleOrderMaxContractsThresholdStateMessage message => SingleOrderMaxContractsThresholdStateMessage.encode message
  | .riskSettingsQueryDoneMessage message => RiskSettingsQueryDoneMessage.encode message
  | .riskSettingsQueryRejMessage message => RiskSettingsQueryRejMessage.encode message
  | .manualCpBreachTriggerRejMessage message => ManualCpBreachTriggerRejMessage.encode message
  | .breachClearRejMessage message => BreachClearRejMessage.encode message
  | .breachClearedMessage message => BreachClearedMessage.encode message
  | .cpGrossNotionalThresholdStateMessage message => CpGrossNotionalThresholdStateMessage.encode message
  | .cpMarketOrderGrossNotionalThresholdStateMessage message => CpMarketOrderGrossNotionalThresholdStateMessage.encode message
  | .cpNetNotionalThresholdStateMessage message => CpNetNotionalThresholdStateMessage.encode message
  | .cpMarketOrderNetNotionalThresholdStateMessage message => CpMarketOrderNetNotionalThresholdStateMessage.encode message
  | .cpDuplicateOrderThresholdStateMessage message => CpDuplicateOrderThresholdStateMessage.encode message
  | .cpOrderRateThresholdStateMessage message => CpOrderRateThresholdStateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 67 := by
  cases message with
  | riskSettingsQueryMessage inner =>
    simp only [encode, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeReqMessage inner =>
    simp only [encode, ActiveRiskThresholdChangeReqMessage.encode_length]
    omega
  | activeRiskAcknowledgementReqMessage inner =>
    simp only [encode, ActiveRiskAcknowledgementReqMessage.encode_length]
    omega
  | cpVolumeThresholdChangeReqMessage inner =>
    simp only [encode, CpVolumeThresholdChangeReqMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeReqMessage inner =>
    simp only [encode, CpExecutedNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeReqMessage inner =>
    simp only [encode, CpTotalExecutionsThresholdChangeReqMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeReqMessage inner =>
    simp only [encode, CpPercentOutstandingContractsThresholdChangeReqMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeReqMessage inner =>
    simp only [encode, CpBreachCountThresholdChangeReqMessage.encode_length]
    omega
  | manualCpBreachTriggerReqMessage inner =>
    simp only [encode, ManualCpBreachTriggerReqMessage.encode_length]
    omega
  | cpClearBreachReqMessage inner =>
    simp only [encode, CpClearBreachReqMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeReqMessage inner =>
    simp only [encode, SingleOrderAllowIsoOrdersChangeReqMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeReqMessage inner =>
    simp only [encode, SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeReqMessage inner =>
    simp only [encode, SingleOrderMaxNotionalChangeReqMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeReqMessage inner =>
    simp only [encode, SingleOrderMaxContractsChangeReqMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeReqMessage inner =>
    simp only [encode, CpGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeReqMessage inner =>
    simp only [encode, CpMarketOrderGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeReqMessage inner =>
    simp only [encode, CpNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeReqMessage inner =>
    simp only [encode, CpMarketOrderNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeReqMessage inner =>
    simp only [encode, CpDuplicateOrderThresholdChangeReqMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeReqMessage inner =>
    simp only [encode, CpOrderRateThresholdChangeReqMessage.encode_length]
    omega
  | activeRiskThresholdStateMessage inner =>
    simp only [encode, ActiveRiskThresholdStateMessage.encode_length]
    omega
  | activeRiskThresholdChangeRejMessage inner =>
    simp only [encode, ActiveRiskThresholdChangeRejMessage.encode_length]
    omega
  | activeRiskAcknowledgedMessage inner =>
    simp only [encode, ActiveRiskAcknowledgedMessage.encode_length]
    omega
  | activeRiskAcknowledgeRejMessage inner =>
    simp only [encode, ActiveRiskAcknowledgeRejMessage.encode_length]
    omega
  | activeRiskQuantityUpdateNotificationMessage inner =>
    simp only [encode, ActiveRiskQuantityUpdateNotificationMessage.encode_length]
    omega
  | cpVolumeThresholdStateMessage inner =>
    simp only [encode, CpVolumeThresholdStateMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdStateMessage inner =>
    simp only [encode, CpExecutedNotionalThresholdStateMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdStateMessage inner =>
    simp only [encode, CpTotalExecutionsThresholdStateMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdStateMessage inner =>
    simp only [encode, CpPercentOutstandingContractsThresholdStateMessage.encode_length]
    omega
  | cpBreachCountThresholdStateMessage inner =>
    simp only [encode, CpBreachCountThresholdStateMessage.encode_length]
    omega
  | manualCpBreachTriggerPendingMessage inner =>
    simp only [encode, ManualCpBreachTriggerPendingMessage.encode_length]
    omega
  | manualCpBreachTriggerDoneMessage inner =>
    simp only [encode, ManualCpBreachTriggerDoneMessage.encode_length]
    omega
  | riskThresholdUpdateRejMessage inner =>
    simp only [encode, RiskThresholdUpdateRejMessage.encode_length]
    omega
  | passiveRiskThresholdNotificationMessage inner =>
    simp only [encode, PassiveRiskThresholdNotificationMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersStateMessage inner =>
    simp only [encode, SingleOrderAllowIsoOrdersStateMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketStateMessage inner =>
    simp only [encode, SingleOrderAllowOrdersInCrossedMarketStateMessage.encode_length]
    omega
  | singleOrderMaxNotionalThresholdStateMessage inner =>
    simp only [encode, SingleOrderMaxNotionalThresholdStateMessage.encode_length]
    omega
  | singleOrderMaxContractsThresholdStateMessage inner =>
    simp only [encode, SingleOrderMaxContractsThresholdStateMessage.encode_length]
    omega
  | riskSettingsQueryDoneMessage inner =>
    simp only [encode, RiskSettingsQueryDoneMessage.encode_length]
    omega
  | riskSettingsQueryRejMessage inner =>
    simp only [encode, RiskSettingsQueryRejMessage.encode_length]
    omega
  | manualCpBreachTriggerRejMessage inner =>
    simp only [encode, ManualCpBreachTriggerRejMessage.encode_length]
    omega
  | breachClearRejMessage inner =>
    simp only [encode, BreachClearRejMessage.encode_length]
    omega
  | breachClearedMessage inner =>
    simp only [encode, BreachClearedMessage.encode_length]
    omega
  | cpGrossNotionalThresholdStateMessage inner =>
    simp only [encode, CpGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdStateMessage inner =>
    simp only [encode, CpMarketOrderGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpNetNotionalThresholdStateMessage inner =>
    simp only [encode, CpNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdStateMessage inner =>
    simp only [encode, CpMarketOrderNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdStateMessage inner =>
    simp only [encode, CpDuplicateOrderThresholdStateMessage.encode_length]
    omega
  | cpOrderRateThresholdStateMessage inner =>
    simp only [encode, CpOrderRateThresholdStateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (RiskSettingsQueryMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryMessage message, rest)
  else if tag = 2 then (ActiveRiskThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdChangeReqMessage message, rest)
  else if tag = 3 then (ActiveRiskAcknowledgementReqMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgementReqMessage message, rest)
  else if tag = 4 then (CpVolumeThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpVolumeThresholdChangeReqMessage message, rest)
  else if tag = 5 then (CpExecutedNotionalThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpExecutedNotionalThresholdChangeReqMessage message, rest)
  else if tag = 6 then (CpTotalExecutionsThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpTotalExecutionsThresholdChangeReqMessage message, rest)
  else if tag = 7 then (CpPercentOutstandingContractsThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpPercentOutstandingContractsThresholdChangeReqMessage message, rest)
  else if tag = 8 then (CpBreachCountThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpBreachCountThresholdChangeReqMessage message, rest)
  else if tag = 9 then (ManualCpBreachTriggerReqMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerReqMessage message, rest)
  else if tag = 10 then (CpClearBreachReqMessage.decode bytes).map fun (message, rest) => (.cpClearBreachReqMessage message, rest)
  else if tag = 11 then (SingleOrderAllowIsoOrdersChangeReqMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowIsoOrdersChangeReqMessage message, rest)
  else if tag = 12 then (SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowOrdersInCrossedMarketChangeReqMessage message, rest)
  else if tag = 13 then (SingleOrderMaxNotionalChangeReqMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxNotionalChangeReqMessage message, rest)
  else if tag = 14 then (SingleOrderMaxContractsChangeReqMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxContractsChangeReqMessage message, rest)
  else if tag = 18 then (CpGrossNotionalThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpGrossNotionalThresholdChangeReqMessage message, rest)
  else if tag = 19 then (CpMarketOrderGrossNotionalThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderGrossNotionalThresholdChangeReqMessage message, rest)
  else if tag = 20 then (CpNetNotionalThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpNetNotionalThresholdChangeReqMessage message, rest)
  else if tag = 21 then (CpMarketOrderNetNotionalThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderNetNotionalThresholdChangeReqMessage message, rest)
  else if tag = 22 then (CpDuplicateOrderThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpDuplicateOrderThresholdChangeReqMessage message, rest)
  else if tag = 23 then (CpOrderRateThresholdChangeReqMessage.decode bytes).map fun (message, rest) => (.cpOrderRateThresholdChangeReqMessage message, rest)
  else if tag = 30 then (ActiveRiskThresholdStateMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdStateMessage message, rest)
  else if tag = 31 then (ActiveRiskThresholdChangeRejMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdChangeRejMessage message, rest)
  else if tag = 32 then (ActiveRiskAcknowledgedMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgedMessage message, rest)
  else if tag = 33 then (ActiveRiskAcknowledgeRejMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgeRejMessage message, rest)
  else if tag = 34 then (ActiveRiskQuantityUpdateNotificationMessage.decode bytes).map fun (message, rest) => (.activeRiskQuantityUpdateNotificationMessage message, rest)
  else if tag = 35 then (CpVolumeThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpVolumeThresholdStateMessage message, rest)
  else if tag = 36 then (CpExecutedNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpExecutedNotionalThresholdStateMessage message, rest)
  else if tag = 37 then (CpTotalExecutionsThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpTotalExecutionsThresholdStateMessage message, rest)
  else if tag = 38 then (CpPercentOutstandingContractsThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpPercentOutstandingContractsThresholdStateMessage message, rest)
  else if tag = 39 then (CpBreachCountThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpBreachCountThresholdStateMessage message, rest)
  else if tag = 40 then (ManualCpBreachTriggerPendingMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerPendingMessage message, rest)
  else if tag = 41 then (ManualCpBreachTriggerDoneMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerDoneMessage message, rest)
  else if tag = 42 then (RiskThresholdUpdateRejMessage.decode bytes).map fun (message, rest) => (.riskThresholdUpdateRejMessage message, rest)
  else if tag = 43 then (PassiveRiskThresholdNotificationMessage.decode bytes).map fun (message, rest) => (.passiveRiskThresholdNotificationMessage message, rest)
  else if tag = 44 then (SingleOrderAllowIsoOrdersStateMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowIsoOrdersStateMessage message, rest)
  else if tag = 45 then (SingleOrderAllowOrdersInCrossedMarketStateMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowOrdersInCrossedMarketStateMessage message, rest)
  else if tag = 46 then (SingleOrderMaxNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxNotionalThresholdStateMessage message, rest)
  else if tag = 47 then (SingleOrderMaxContractsThresholdStateMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxContractsThresholdStateMessage message, rest)
  else if tag = 48 then (RiskSettingsQueryDoneMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryDoneMessage message, rest)
  else if tag = 49 then (RiskSettingsQueryRejMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryRejMessage message, rest)
  else if tag = 50 then (ManualCpBreachTriggerRejMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerRejMessage message, rest)
  else if tag = 51 then (BreachClearRejMessage.decode bytes).map fun (message, rest) => (.breachClearRejMessage message, rest)
  else if tag = 52 then (BreachClearedMessage.decode bytes).map fun (message, rest) => (.breachClearedMessage message, rest)
  else if tag = 60 then (CpGrossNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpGrossNotionalThresholdStateMessage message, rest)
  else if tag = 61 then (CpMarketOrderGrossNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderGrossNotionalThresholdStateMessage message, rest)
  else if tag = 62 then (CpNetNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpNetNotionalThresholdStateMessage message, rest)
  else if tag = 63 then (CpMarketOrderNetNotionalThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderNetNotionalThresholdStateMessage message, rest)
  else if tag = 64 then (CpDuplicateOrderThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpDuplicateOrderThresholdStateMessage message, rest)
  else if tag = 65 then (CpOrderRateThresholdStateMessage.decode bytes).map fun (message, rest) => (.cpOrderRateThresholdStateMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 73 := by
  unfold encode
  cases message.payload with
  | riskSettingsQueryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeReqMessage.encode_length]
    omega
  | activeRiskAcknowledgementReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgementReqMessage.encode_length]
    omega
  | cpVolumeThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdChangeReqMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdChangeReqMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdChangeReqMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdChangeReqMessage.encode_length]
    omega
  | manualCpBreachTriggerReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerReqMessage.encode_length]
    omega
  | cpClearBreachReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearBreachReqMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersChangeReqMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalChangeReqMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsChangeReqMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdChangeReqMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeReqMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdChangeReqMessage.encode_length]
    omega
  | activeRiskThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdStateMessage.encode_length]
    omega
  | activeRiskThresholdChangeRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeRejMessage.encode_length]
    omega
  | activeRiskAcknowledgedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgedMessage.encode_length]
    omega
  | activeRiskAcknowledgeRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgeRejMessage.encode_length]
    omega
  | activeRiskQuantityUpdateNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskQuantityUpdateNotificationMessage.encode_length]
    omega
  | cpVolumeThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdStateMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdStateMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdStateMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdStateMessage.encode_length]
    omega
  | cpBreachCountThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdStateMessage.encode_length]
    omega
  | manualCpBreachTriggerPendingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerPendingMessage.encode_length]
    omega
  | manualCpBreachTriggerDoneMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerDoneMessage.encode_length]
    omega
  | riskThresholdUpdateRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskThresholdUpdateRejMessage.encode_length]
    omega
  | passiveRiskThresholdNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PassiveRiskThresholdNotificationMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersStateMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketStateMessage.encode_length]
    omega
  | singleOrderMaxNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalThresholdStateMessage.encode_length]
    omega
  | singleOrderMaxContractsThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsThresholdStateMessage.encode_length]
    omega
  | riskSettingsQueryDoneMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryDoneMessage.encode_length]
    omega
  | riskSettingsQueryRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryRejMessage.encode_length]
    omega
  | manualCpBreachTriggerRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerRejMessage.encode_length]
    omega
  | breachClearRejMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearRejMessage.encode_length]
    omega
  | breachClearedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BreachClearedMessage.encode_length]
    omega
  | cpGrossNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdStateMessage.encode_length]
    omega
  | cpNetNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdStateMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdStateMessage.encode_length]
    omega
  | cpOrderRateThresholdStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdStateMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end UnsequencedMessage

/-- Any Client Data, selected by Message Type -/
inductive ClientData where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  deriving DecidableEq, Repr

namespace ClientData

/-- The Message Type each message is sent under -/
def tag : ClientData → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104

def encode : ClientData → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientData × List UInt8) :=
  if tag = 100 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 101 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).map fun (message, rest) => (.replayAllRequestMessage message, rest)
  else if tag = 103 then (StreamRequestMessage.decode bytes).map fun (message, rest) => (.streamRequestMessage message, rest)
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun (message, rest) => (.unsequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientData

/-- Client Packet -/
structure ClientPacket where
  messageLength : BitVec 16
  clientData : ClientData
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientData.tag message.clientData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientData.encode message.clientData))

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientData, bytes) ← ClientData.decode messageType bytes
  pure ({ messageLength, clientData }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientData.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.MemxMemxoptionsRiskcontrolSbeV16Client
