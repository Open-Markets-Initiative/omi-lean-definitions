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

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
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
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 8
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

def encode : ClientPayload → List UInt8
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

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 44 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
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
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Sbe Message -/
structure ClientSbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSbeMessage

def encode (message : ClientSbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (ClientPayload.encode message.clientPayload))))

def decode (bytes : List UInt8) : Option (ClientSbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, clientPayload }, bytes)

theorem encode_length_pos (message : ClientSbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientSbeMessage) : (encode message).length ≤ 50 := by
  unfold encode
  cases message.clientPayload with
  | riskSettingsQueryMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeReqMessage.encode_length]
    omega
  | activeRiskAcknowledgementReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgementReqMessage.encode_length]
    omega
  | cpVolumeThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdChangeReqMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdChangeReqMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdChangeReqMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdChangeReqMessage.encode_length]
    omega
  | manualCpBreachTriggerReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerReqMessage.encode_length]
    omega
  | cpClearBreachReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearBreachReqMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersChangeReqMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalChangeReqMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsChangeReqMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdChangeReqMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdChangeReqMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeReqMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdChangeReqMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientSbeMessage) (rest : List UInt8) :
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
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientSbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  clientSbeMessage : ClientSbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  ClientSbeMessage.encode message.clientSbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (clientSbeMessage, bytes) ← ClientSbeMessage.decode bytes
  pure ({ clientSbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := ClientSbeMessage.encode_length_pos message.clientSbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ClientSbeMessage.decode_encode, some_bind]
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
