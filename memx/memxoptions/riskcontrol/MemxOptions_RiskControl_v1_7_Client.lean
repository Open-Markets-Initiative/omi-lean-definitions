import Wire

/-!
# The Members Exchange Risk Control v1.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsRiskcontrolSbeV17Client

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

/-- Active Risk Threshold Change Request Message: 34 bytes -/
structure ActiveRiskThresholdChangeRequestMessage where
  clOrdIdActiveRiskThresholdChangeRequestClOrdId : Alpha 20
  underlierActiveRiskThresholdChangeRequestUnderlierOptional : Alpha 6
  efidActiveRiskThresholdChangeRequestEfidOptional : Alpha 4
  thresholdQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskThresholdChangeRequestMessage

def encode (message : ActiveRiskThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidActiveRiskThresholdChangeRequestEfidOptional
    ++ (encodeUInt 4 message.thresholdQuantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (thresholdQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdActiveRiskThresholdChangeRequestClOrdId, underlierActiveRiskThresholdChangeRequestUnderlierOptional, efidActiveRiskThresholdChangeRequestEfidOptional, thresholdQuantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskThresholdChangeRequestMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskThresholdChangeRequestMessage) (rest : List UInt8) :
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

end ActiveRiskThresholdChangeRequestMessage

/-- Active Risk Acknowledgement Request Message: 34 bytes -/
structure ActiveRiskAcknowledgementRequestMessage where
  clOrdIdActiveRiskAcknowledgementRequestClOrdId : Alpha 20
  underlierActiveRiskAcknowledgementRequestUnderlier : Alpha 6
  efidActiveRiskAcknowledgementRequestEfid : Alpha 4
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgementRequestMessage

def encode (message : ActiveRiskAcknowledgementRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskAcknowledgementRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskAcknowledgementRequestUnderlier
    ++ (Alpha.encode message.efidActiveRiskAcknowledgementRequestEfid
    ++ (encodeUInt 4 message.quantity)))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgementRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskAcknowledgementRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskAcknowledgementRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskAcknowledgementRequestEfid, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdActiveRiskAcknowledgementRequestClOrdId, underlierActiveRiskAcknowledgementRequestUnderlier, efidActiveRiskAcknowledgementRequestEfid, quantity }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgementRequestMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgementRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgementRequestMessage) (rest : List UInt8) :
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

end ActiveRiskAcknowledgementRequestMessage

/-- Cp Volume Threshold Change Request Message: 44 bytes -/
structure CpVolumeThresholdChangeRequestMessage where
  clOrdIdCpVolumeThresholdChangeRequestClOrdId : Alpha 20
  underlierCpVolumeThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpVolumeThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  volume : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpVolumeThresholdChangeRequestMessage

def encode (message : CpVolumeThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpVolumeThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpVolumeThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpVolumeThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpVolumeThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpVolumeThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpVolumeThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpVolumeThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpVolumeThresholdChangeRequestClOrdId, underlierCpVolumeThresholdChangeRequestUnderlierOptional, efidCpVolumeThresholdChangeRequestEfidOptional, riskGroupId, volume, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpVolumeThresholdChangeRequestMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpVolumeThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpVolumeThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpVolumeThresholdChangeRequestMessage

/-- Cp Executed Notional Threshold Change Request Message: 44 bytes -/
structure CpExecutedNotionalThresholdChangeRequestMessage where
  clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpExecutedNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpExecutedNotionalThresholdChangeRequestMessage

def encode (message : CpExecutedNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpExecutedNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpExecutedNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpExecutedNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpExecutedNotionalThresholdChangeRequestClOrdId, underlierCpExecutedNotionalThresholdChangeRequestUnderlierOptional, efidCpExecutedNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpExecutedNotionalThresholdChangeRequestMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpExecutedNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpExecutedNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpExecutedNotionalThresholdChangeRequestMessage

/-- Cp Total Executions Threshold Change Request Message: 40 bytes -/
structure CpTotalExecutionsThresholdChangeRequestMessage where
  clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId : Alpha 20
  underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpTotalExecutionsThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  totalExecutions : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpTotalExecutionsThresholdChangeRequestMessage

def encode (message : CpTotalExecutionsThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpTotalExecutionsThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.totalExecutions
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpTotalExecutionsThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpTotalExecutionsThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (totalExecutions, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpTotalExecutionsThresholdChangeRequestClOrdId, underlierCpTotalExecutionsThresholdChangeRequestUnderlierOptional, efidCpTotalExecutionsThresholdChangeRequestEfidOptional, riskGroupId, totalExecutions, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpTotalExecutionsThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpTotalExecutionsThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpTotalExecutionsThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpTotalExecutionsThresholdChangeRequestMessage

/-- Cp Percent Outstanding Contracts Threshold Change Request Message: 38 bytes -/
structure CpPercentOutstandingContractsThresholdChangeRequestMessage where
  clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId : Alpha 20
  underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional : Alpha 4
  percent : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpPercentOutstandingContractsThresholdChangeRequestMessage

def encode (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional
    ++ (encodeUInt 4 message.percent
    ++ (encodeUInt 4 message.periodInMilliSeconds))))

def decode (bytes : List UInt8) : Option (CpPercentOutstandingContractsThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (percent, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpPercentOutstandingContractsThresholdChangeRequestClOrdId, underlierCpPercentOutstandingContractsThresholdChangeRequestUnderlierOptional, efidCpPercentOutstandingContractsThresholdChangeRequestEfidOptional, percent, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpPercentOutstandingContractsThresholdChangeRequestMessage

/-- Cp Breach Count Threshold Change Request Message: 40 bytes -/
structure CpBreachCountThresholdChangeRequestMessage where
  clOrdIdCpBreachCountThresholdChangeRequestClOrdId : Alpha 20
  underlierCpBreachCountThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpBreachCountThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  count : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpBreachCountThresholdChangeRequestMessage

def encode (message : CpBreachCountThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpBreachCountThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpBreachCountThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpBreachCountThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.count
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpBreachCountThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpBreachCountThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpBreachCountThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpBreachCountThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpBreachCountThresholdChangeRequestClOrdId, underlierCpBreachCountThresholdChangeRequestUnderlierOptional, efidCpBreachCountThresholdChangeRequestEfidOptional, riskGroupId, count, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpBreachCountThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpBreachCountThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpBreachCountThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpBreachCountThresholdChangeRequestMessage

/-- Manual Cp Breach Trigger Request Message: 33 bytes -/
structure ManualCpBreachTriggerRequestMessage where
  clOrdIdManualCpBreachTriggerRequestClOrdId : Alpha 20
  underlierManualCpBreachTriggerRequestUnderlierOptional : Alpha 6
  efidManualCpBreachTriggerRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  sendCancels : BitVec 8
  deriving DecidableEq, Repr

namespace ManualCpBreachTriggerRequestMessage

def encode (message : ManualCpBreachTriggerRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdManualCpBreachTriggerRequestClOrdId
    ++ (Alpha.encode message.underlierManualCpBreachTriggerRequestUnderlierOptional
    ++ (Alpha.encode message.efidManualCpBreachTriggerRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.sendCancels))))

def decode (bytes : List UInt8) : Option (ManualCpBreachTriggerRequestMessage × List UInt8) := do
  let (clOrdIdManualCpBreachTriggerRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierManualCpBreachTriggerRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidManualCpBreachTriggerRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (sendCancels, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdManualCpBreachTriggerRequestClOrdId, underlierManualCpBreachTriggerRequestUnderlierOptional, efidManualCpBreachTriggerRequestEfidOptional, riskGroupId, sendCancels }, bytes)

@[simp] theorem encode_length (message : ManualCpBreachTriggerRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ManualCpBreachTriggerRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualCpBreachTriggerRequestMessage) (rest : List UInt8) :
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

end ManualCpBreachTriggerRequestMessage

/-- Cp Clear Breach Request Message: 28 bytes -/
structure CpClearBreachRequestMessage where
  clOrdIdCpClearBreachRequestClOrdId : Alpha 20
  breachId : BitVec 64
  deriving DecidableEq, Repr

namespace CpClearBreachRequestMessage

def encode (message : CpClearBreachRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearBreachRequestClOrdId
    ++ (encodeUInt 8 message.breachId)

def decode (bytes : List UInt8) : Option (CpClearBreachRequestMessage × List UInt8) := do
  let (clOrdIdCpClearBreachRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (breachId, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpClearBreachRequestClOrdId, breachId }, bytes)

@[simp] theorem encode_length (message : CpClearBreachRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpClearBreachRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearBreachRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CpClearBreachRequestMessage

/-- Single Order Allow Iso Orders Change Request Message: 33 bytes -/
structure SingleOrderAllowIsoOrdersChangeRequestMessage where
  clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowIsoOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowIsoOrdersChangeRequestMessage

def encode (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowIsoOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowIsoOrdersChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowIsoOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowIsoOrdersChangeRequestClOrdId, underlierSingleOrderAllowIsoOrdersChangeRequestUnderlierOptional, efidSingleOrderAllowIsoOrdersChangeRequestEfidOptional, riskGroupId, allowIsoOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowIsoOrdersChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowIsoOrdersChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderAllowIsoOrdersChangeRequestMessage

/-- Single Order Allow Orders In Crossed Market Change Request Message: 33 bytes -/
structure SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage where
  clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage

def encode (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowOrdersInCrossedMarketChangeRequestClOrdId, underlierSingleOrderAllowOrdersInCrossedMarketChangeRequestUnderlierOptional, efidSingleOrderAllowOrdersInCrossedMarketChangeRequestEfidOptional, riskGroupId, allowOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage

/-- Single Order Max Notional Change Request Message: 40 bytes -/
structure SingleOrderMaxNotionalChangeRequestMessage where
  clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId : Alpha 20
  underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderMaxNotionalChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxNotionalInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace SingleOrderMaxNotionalChangeRequestMessage

def encode (message : SingleOrderMaxNotionalChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderMaxNotionalChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.maxNotionalInDollars))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxNotionalChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderMaxNotionalChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxNotionalInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdSingleOrderMaxNotionalChangeRequestClOrdId, underlierSingleOrderMaxNotionalChangeRequestUnderlierOptional, efidSingleOrderMaxNotionalChangeRequestEfidOptional, riskGroupId, maxNotionalInDollars }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxNotionalChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxNotionalChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxNotionalChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderMaxNotionalChangeRequestMessage

/-- Single Order Max Contracts Change Request Message: 36 bytes -/
structure SingleOrderMaxContractsChangeRequestMessage where
  clOrdIdSingleOrderMaxContractsChangeRequestClOrdId : Alpha 20
  underlierSingleOrderMaxContractsChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderMaxContractsChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleOrderMaxContractsChangeRequestMessage

def encode (message : SingleOrderMaxContractsChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderMaxContractsChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderMaxContractsChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderMaxContractsChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxContracts))))

def decode (bytes : List UInt8) : Option (SingleOrderMaxContractsChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderMaxContractsChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderMaxContractsChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderMaxContractsChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxContracts, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdSingleOrderMaxContractsChangeRequestClOrdId, underlierSingleOrderMaxContractsChangeRequestUnderlierOptional, efidSingleOrderMaxContractsChangeRequestEfidOptional, riskGroupId, maxContracts }, bytes)

@[simp] theorem encode_length (message : SingleOrderMaxContractsChangeRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderMaxContractsChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderMaxContractsChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderMaxContractsChangeRequestMessage

/-- Single Order Allow Market Orders Change Request Message: 33 bytes -/
structure SingleOrderAllowMarketOrdersChangeRequestMessage where
  clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId : Alpha 20
  underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional : Alpha 6
  efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  allowMarketOrders : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderAllowMarketOrdersChangeRequestMessage

def encode (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.allowMarketOrders))))

def decode (bytes : List UInt8) : Option (SingleOrderAllowMarketOrdersChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (allowMarketOrders, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderAllowMarketOrdersChangeRequestClOrdId, underlierSingleOrderAllowMarketOrdersChangeRequestUnderlierOptional, efidSingleOrderAllowMarketOrdersChangeRequestEfidOptional, riskGroupId, allowMarketOrders }, bytes)

@[simp] theorem encode_length (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderAllowMarketOrdersChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderAllowMarketOrdersChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderAllowMarketOrdersChangeRequestMessage

/-- Single Order Restricted Underlier Change Request Message: 33 bytes -/
structure SingleOrderRestrictedUnderlierChangeRequestMessage where
  clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId : Alpha 20
  underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier : Alpha 6
  efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  restricted : BitVec 8
  deriving DecidableEq, Repr

namespace SingleOrderRestrictedUnderlierChangeRequestMessage

def encode (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId
    ++ (Alpha.encode message.underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier
    ++ (Alpha.encode message.efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.restricted))))

def decode (bytes : List UInt8) : Option (SingleOrderRestrictedUnderlierChangeRequestMessage × List UInt8) := do
  let (clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (restricted, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdIdSingleOrderRestrictedUnderlierChangeRequestClOrdId, underlierSingleOrderRestrictedUnderlierChangeRequestUnderlier, efidSingleOrderRestrictedUnderlierChangeRequestEfidOptional, riskGroupId, restricted }, bytes)

@[simp] theorem encode_length (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleOrderRestrictedUnderlierChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleOrderRestrictedUnderlierChangeRequestMessage) (rest : List UInt8) :
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

end SingleOrderRestrictedUnderlierChangeRequestMessage

/-- Cp Gross Notional Threshold Change Request Message: 40 bytes -/
structure CpGrossNotionalThresholdChangeRequestMessage where
  clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpGrossNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpGrossNotionalThresholdChangeRequestMessage

def encode (message : CpGrossNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpGrossNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpGrossNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpGrossNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpGrossNotionalThresholdChangeRequestClOrdId, underlierCpGrossNotionalThresholdChangeRequestUnderlierOptional, efidCpGrossNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpGrossNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpGrossNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpGrossNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpGrossNotionalThresholdChangeRequestMessage

/-- Cp Market Order Gross Notional Threshold Change Request Message: 40 bytes -/
structure CpMarketOrderGrossNotionalThresholdChangeRequestMessage where
  clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderGrossNotionalThresholdChangeRequestMessage

def encode (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderGrossNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpMarketOrderGrossNotionalThresholdChangeRequestClOrdId, underlierCpMarketOrderGrossNotionalThresholdChangeRequestUnderlierOptional, efidCpMarketOrderGrossNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpMarketOrderGrossNotionalThresholdChangeRequestMessage

/-- Cp Net Notional Threshold Change Request Message: 40 bytes -/
structure CpNetNotionalThresholdChangeRequestMessage where
  clOrdIdCpNetNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpNetNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpNetNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpNetNotionalThresholdChangeRequestMessage

def encode (message : CpNetNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpNetNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpNetNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpNetNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpNetNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpNetNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpNetNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpNetNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpNetNotionalThresholdChangeRequestClOrdId, underlierCpNetNotionalThresholdChangeRequestUnderlierOptional, efidCpNetNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpNetNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpNetNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpNetNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpNetNotionalThresholdChangeRequestMessage

/-- Cp Market Order Net Notional Threshold Change Request Message: 40 bytes -/
structure CpMarketOrderNetNotionalThresholdChangeRequestMessage where
  clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId : Alpha 20
  underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  priceInDollars : BitVec 64
  deriving DecidableEq, Repr

namespace CpMarketOrderNetNotionalThresholdChangeRequestMessage

def encode (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 8 message.priceInDollars))))

def decode (bytes : List UInt8) : Option (CpMarketOrderNetNotionalThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (priceInDollars, bytes) ← decodeUInt 8 bytes
  pure ({ clOrdIdCpMarketOrderNetNotionalThresholdChangeRequestClOrdId, underlierCpMarketOrderNetNotionalThresholdChangeRequestUnderlierOptional, efidCpMarketOrderNetNotionalThresholdChangeRequestEfidOptional, riskGroupId, priceInDollars }, bytes)

@[simp] theorem encode_length (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpMarketOrderNetNotionalThresholdChangeRequestMessage

/-- Cp Duplicate Order Threshold Change Request Message: 41 bytes -/
structure CpDuplicateOrderThresholdChangeRequestMessage where
  clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId : Alpha 20
  underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpDuplicateOrderThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxDupOrders : BitVec 32
  useOrderPriceInDupCheckOptional : BitVec 8
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpDuplicateOrderThresholdChangeRequestMessage

def encode (message : CpDuplicateOrderThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpDuplicateOrderThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxDupOrders
    ++ (encodeUInt 1 message.useOrderPriceInDupCheckOptional
    ++ (encodeUInt 4 message.periodInMilliSeconds))))))

def decode (bytes : List UInt8) : Option (CpDuplicateOrderThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpDuplicateOrderThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxDupOrders, bytes) ← decodeUInt 4 bytes
  let (useOrderPriceInDupCheckOptional, bytes) ← decodeUInt 1 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpDuplicateOrderThresholdChangeRequestClOrdId, underlierCpDuplicateOrderThresholdChangeRequestUnderlierOptional, efidCpDuplicateOrderThresholdChangeRequestEfidOptional, riskGroupId, maxDupOrders, useOrderPriceInDupCheckOptional, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpDuplicateOrderThresholdChangeRequestMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpDuplicateOrderThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpDuplicateOrderThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpDuplicateOrderThresholdChangeRequestMessage

/-- Cp Order Rate Threshold Change Request Message: 40 bytes -/
structure CpOrderRateThresholdChangeRequestMessage where
  clOrdIdCpOrderRateThresholdChangeRequestClOrdId : Alpha 20
  underlierCpOrderRateThresholdChangeRequestUnderlierOptional : Alpha 6
  efidCpOrderRateThresholdChangeRequestEfidOptional : Alpha 4
  riskGroupId : BitVec 16
  maxOrderMsgs : BitVec 32
  periodInMilliSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace CpOrderRateThresholdChangeRequestMessage

def encode (message : CpOrderRateThresholdChangeRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpOrderRateThresholdChangeRequestClOrdId
    ++ (Alpha.encode message.underlierCpOrderRateThresholdChangeRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpOrderRateThresholdChangeRequestEfidOptional
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.maxOrderMsgs
    ++ (encodeUInt 4 message.periodInMilliSeconds)))))

def decode (bytes : List UInt8) : Option (CpOrderRateThresholdChangeRequestMessage × List UInt8) := do
  let (clOrdIdCpOrderRateThresholdChangeRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpOrderRateThresholdChangeRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpOrderRateThresholdChangeRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (maxOrderMsgs, bytes) ← decodeUInt 4 bytes
  let (periodInMilliSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ clOrdIdCpOrderRateThresholdChangeRequestClOrdId, underlierCpOrderRateThresholdChangeRequestUnderlierOptional, efidCpOrderRateThresholdChangeRequestEfidOptional, riskGroupId, maxOrderMsgs, periodInMilliSeconds }, bytes)

@[simp] theorem encode_length (message : CpOrderRateThresholdChangeRequestMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CpOrderRateThresholdChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpOrderRateThresholdChangeRequestMessage) (rest : List UInt8) :
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

end CpOrderRateThresholdChangeRequestMessage

/-- Cp Clear All Breaches Request Message: 20 bytes -/
structure CpClearAllBreachesRequestMessage where
  clOrdIdCpClearAllBreachesRequestClOrdId : Alpha 20
  deriving DecidableEq, Repr

namespace CpClearAllBreachesRequestMessage

def encode (message : CpClearAllBreachesRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearAllBreachesRequestClOrdId

def decode (bytes : List UInt8) : Option (CpClearAllBreachesRequestMessage × List UInt8) := do
  let (clOrdIdCpClearAllBreachesRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  pure ({ clOrdIdCpClearAllBreachesRequestClOrdId }, bytes)

@[simp] theorem encode_length (message : CpClearAllBreachesRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CpClearAllBreachesRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearAllBreachesRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CpClearAllBreachesRequestMessage

/-- Cp Clear All Breaches By Efid Or Underlier Request Message: 30 bytes -/
structure CpClearAllBreachesByEfidOrUnderlierRequestMessage where
  clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId : Alpha 20
  underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional : Alpha 6
  efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional : Alpha 4
  deriving DecidableEq, Repr

namespace CpClearAllBreachesByEfidOrUnderlierRequestMessage

def encode (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId
    ++ (Alpha.encode message.underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional
    ++ (Alpha.encode message.efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional))

def decode (bytes : List UInt8) : Option (CpClearAllBreachesByEfidOrUnderlierRequestMessage × List UInt8) := do
  let (clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional, bytes) ← Alpha.decode 6 bytes
  let (efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ clOrdIdCpClearAllBreachesByEfidOrUnderlierRequestClOrdId, underlierCpClearAllBreachesByEfidOrUnderlierRequestUnderlierOptional, efidCpClearAllBreachesByEfidOrUnderlierRequestEfidOptional }, bytes)

@[simp] theorem encode_length (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CpClearAllBreachesByEfidOrUnderlierRequestMessage

/-- Active Risk Acknowledge All Request Message: 30 bytes -/
structure ActiveRiskAcknowledgeAllRequestMessage where
  clOrdIdActiveRiskAcknowledgeAllRequestClOrdId : Alpha 20
  underlierActiveRiskAcknowledgeAllRequestUnderlier : Alpha 6
  efidActiveRiskAcknowledgeAllRequestEfid : Alpha 4
  deriving DecidableEq, Repr

namespace ActiveRiskAcknowledgeAllRequestMessage

def encode (message : ActiveRiskAcknowledgeAllRequestMessage) : List UInt8 :=
  Alpha.encode message.clOrdIdActiveRiskAcknowledgeAllRequestClOrdId
    ++ (Alpha.encode message.underlierActiveRiskAcknowledgeAllRequestUnderlier
    ++ (Alpha.encode message.efidActiveRiskAcknowledgeAllRequestEfid))

def decode (bytes : List UInt8) : Option (ActiveRiskAcknowledgeAllRequestMessage × List UInt8) := do
  let (clOrdIdActiveRiskAcknowledgeAllRequestClOrdId, bytes) ← Alpha.decode 20 bytes
  let (underlierActiveRiskAcknowledgeAllRequestUnderlier, bytes) ← Alpha.decode 6 bytes
  let (efidActiveRiskAcknowledgeAllRequestEfid, bytes) ← Alpha.decode 4 bytes
  pure ({ clOrdIdActiveRiskAcknowledgeAllRequestClOrdId, underlierActiveRiskAcknowledgeAllRequestUnderlier, efidActiveRiskAcknowledgeAllRequestEfid }, bytes)

@[simp] theorem encode_length (message : ActiveRiskAcknowledgeAllRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ActiveRiskAcknowledgeAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveRiskAcknowledgeAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ActiveRiskAcknowledgeAllRequestMessage

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | riskSettingsQueryMessage (message : RiskSettingsQueryMessage) -- 1
  | activeRiskThresholdChangeRequestMessage (message : ActiveRiskThresholdChangeRequestMessage) -- 2
  | activeRiskAcknowledgementRequestMessage (message : ActiveRiskAcknowledgementRequestMessage) -- 3
  | cpVolumeThresholdChangeRequestMessage (message : CpVolumeThresholdChangeRequestMessage) -- 4
  | cpExecutedNotionalThresholdChangeRequestMessage (message : CpExecutedNotionalThresholdChangeRequestMessage) -- 5
  | cpTotalExecutionsThresholdChangeRequestMessage (message : CpTotalExecutionsThresholdChangeRequestMessage) -- 6
  | cpPercentOutstandingContractsThresholdChangeRequestMessage (message : CpPercentOutstandingContractsThresholdChangeRequestMessage) -- 7
  | cpBreachCountThresholdChangeRequestMessage (message : CpBreachCountThresholdChangeRequestMessage) -- 8
  | manualCpBreachTriggerRequestMessage (message : ManualCpBreachTriggerRequestMessage) -- 9
  | cpClearBreachRequestMessage (message : CpClearBreachRequestMessage) -- 10
  | singleOrderAllowIsoOrdersChangeRequestMessage (message : SingleOrderAllowIsoOrdersChangeRequestMessage) -- 11
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage (message : SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage) -- 12
  | singleOrderMaxNotionalChangeRequestMessage (message : SingleOrderMaxNotionalChangeRequestMessage) -- 13
  | singleOrderMaxContractsChangeRequestMessage (message : SingleOrderMaxContractsChangeRequestMessage) -- 14
  | singleOrderAllowMarketOrdersChangeRequestMessage (message : SingleOrderAllowMarketOrdersChangeRequestMessage) -- 15
  | singleOrderRestrictedUnderlierChangeRequestMessage (message : SingleOrderRestrictedUnderlierChangeRequestMessage) -- 16
  | cpGrossNotionalThresholdChangeRequestMessage (message : CpGrossNotionalThresholdChangeRequestMessage) -- 18
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage (message : CpMarketOrderGrossNotionalThresholdChangeRequestMessage) -- 19
  | cpNetNotionalThresholdChangeRequestMessage (message : CpNetNotionalThresholdChangeRequestMessage) -- 20
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage (message : CpMarketOrderNetNotionalThresholdChangeRequestMessage) -- 21
  | cpDuplicateOrderThresholdChangeRequestMessage (message : CpDuplicateOrderThresholdChangeRequestMessage) -- 22
  | cpOrderRateThresholdChangeRequestMessage (message : CpOrderRateThresholdChangeRequestMessage) -- 23
  | cpClearAllBreachesRequestMessage (message : CpClearAllBreachesRequestMessage) -- 24
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage (message : CpClearAllBreachesByEfidOrUnderlierRequestMessage) -- 25
  | activeRiskAcknowledgeAllRequestMessage (message : ActiveRiskAcknowledgeAllRequestMessage) -- 26
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .riskSettingsQueryMessage _ => 1
  | .activeRiskThresholdChangeRequestMessage _ => 2
  | .activeRiskAcknowledgementRequestMessage _ => 3
  | .cpVolumeThresholdChangeRequestMessage _ => 4
  | .cpExecutedNotionalThresholdChangeRequestMessage _ => 5
  | .cpTotalExecutionsThresholdChangeRequestMessage _ => 6
  | .cpPercentOutstandingContractsThresholdChangeRequestMessage _ => 7
  | .cpBreachCountThresholdChangeRequestMessage _ => 8
  | .manualCpBreachTriggerRequestMessage _ => 9
  | .cpClearBreachRequestMessage _ => 10
  | .singleOrderAllowIsoOrdersChangeRequestMessage _ => 11
  | .singleOrderAllowOrdersInCrossedMarketChangeRequestMessage _ => 12
  | .singleOrderMaxNotionalChangeRequestMessage _ => 13
  | .singleOrderMaxContractsChangeRequestMessage _ => 14
  | .singleOrderAllowMarketOrdersChangeRequestMessage _ => 15
  | .singleOrderRestrictedUnderlierChangeRequestMessage _ => 16
  | .cpGrossNotionalThresholdChangeRequestMessage _ => 18
  | .cpMarketOrderGrossNotionalThresholdChangeRequestMessage _ => 19
  | .cpNetNotionalThresholdChangeRequestMessage _ => 20
  | .cpMarketOrderNetNotionalThresholdChangeRequestMessage _ => 21
  | .cpDuplicateOrderThresholdChangeRequestMessage _ => 22
  | .cpOrderRateThresholdChangeRequestMessage _ => 23
  | .cpClearAllBreachesRequestMessage _ => 24
  | .cpClearAllBreachesByEfidOrUnderlierRequestMessage _ => 25
  | .activeRiskAcknowledgeAllRequestMessage _ => 26

def encode : ClientPayload → List UInt8
  | .riskSettingsQueryMessage message => RiskSettingsQueryMessage.encode message
  | .activeRiskThresholdChangeRequestMessage message => ActiveRiskThresholdChangeRequestMessage.encode message
  | .activeRiskAcknowledgementRequestMessage message => ActiveRiskAcknowledgementRequestMessage.encode message
  | .cpVolumeThresholdChangeRequestMessage message => CpVolumeThresholdChangeRequestMessage.encode message
  | .cpExecutedNotionalThresholdChangeRequestMessage message => CpExecutedNotionalThresholdChangeRequestMessage.encode message
  | .cpTotalExecutionsThresholdChangeRequestMessage message => CpTotalExecutionsThresholdChangeRequestMessage.encode message
  | .cpPercentOutstandingContractsThresholdChangeRequestMessage message => CpPercentOutstandingContractsThresholdChangeRequestMessage.encode message
  | .cpBreachCountThresholdChangeRequestMessage message => CpBreachCountThresholdChangeRequestMessage.encode message
  | .manualCpBreachTriggerRequestMessage message => ManualCpBreachTriggerRequestMessage.encode message
  | .cpClearBreachRequestMessage message => CpClearBreachRequestMessage.encode message
  | .singleOrderAllowIsoOrdersChangeRequestMessage message => SingleOrderAllowIsoOrdersChangeRequestMessage.encode message
  | .singleOrderAllowOrdersInCrossedMarketChangeRequestMessage message => SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode message
  | .singleOrderMaxNotionalChangeRequestMessage message => SingleOrderMaxNotionalChangeRequestMessage.encode message
  | .singleOrderMaxContractsChangeRequestMessage message => SingleOrderMaxContractsChangeRequestMessage.encode message
  | .singleOrderAllowMarketOrdersChangeRequestMessage message => SingleOrderAllowMarketOrdersChangeRequestMessage.encode message
  | .singleOrderRestrictedUnderlierChangeRequestMessage message => SingleOrderRestrictedUnderlierChangeRequestMessage.encode message
  | .cpGrossNotionalThresholdChangeRequestMessage message => CpGrossNotionalThresholdChangeRequestMessage.encode message
  | .cpMarketOrderGrossNotionalThresholdChangeRequestMessage message => CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode message
  | .cpNetNotionalThresholdChangeRequestMessage message => CpNetNotionalThresholdChangeRequestMessage.encode message
  | .cpMarketOrderNetNotionalThresholdChangeRequestMessage message => CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode message
  | .cpDuplicateOrderThresholdChangeRequestMessage message => CpDuplicateOrderThresholdChangeRequestMessage.encode message
  | .cpOrderRateThresholdChangeRequestMessage message => CpOrderRateThresholdChangeRequestMessage.encode message
  | .cpClearAllBreachesRequestMessage message => CpClearAllBreachesRequestMessage.encode message
  | .cpClearAllBreachesByEfidOrUnderlierRequestMessage message => CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode message
  | .activeRiskAcknowledgeAllRequestMessage message => ActiveRiskAcknowledgeAllRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 44 := by
  cases message with
  | riskSettingsQueryMessage inner =>
    simp only [encode, RiskSettingsQueryMessage.encode_length]
    omega
  | activeRiskThresholdChangeRequestMessage inner =>
    simp only [encode, ActiveRiskThresholdChangeRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgementRequestMessage inner =>
    simp only [encode, ActiveRiskAcknowledgementRequestMessage.encode_length]
    omega
  | cpVolumeThresholdChangeRequestMessage inner =>
    simp only [encode, CpVolumeThresholdChangeRequestMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpExecutedNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeRequestMessage inner =>
    simp only [encode, CpTotalExecutionsThresholdChangeRequestMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeRequestMessage inner =>
    simp only [encode, CpPercentOutstandingContractsThresholdChangeRequestMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeRequestMessage inner =>
    simp only [encode, CpBreachCountThresholdChangeRequestMessage.encode_length]
    omega
  | manualCpBreachTriggerRequestMessage inner =>
    simp only [encode, ManualCpBreachTriggerRequestMessage.encode_length]
    omega
  | cpClearBreachRequestMessage inner =>
    simp only [encode, CpClearBreachRequestMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowIsoOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeRequestMessage inner =>
    simp only [encode, SingleOrderMaxNotionalChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeRequestMessage inner =>
    simp only [encode, SingleOrderMaxContractsChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersChangeRequestMessage inner =>
    simp only [encode, SingleOrderAllowMarketOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierChangeRequestMessage inner =>
    simp only [encode, SingleOrderRestrictedUnderlierChangeRequestMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage inner =>
    simp only [encode, CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeRequestMessage inner =>
    simp only [encode, CpDuplicateOrderThresholdChangeRequestMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeRequestMessage inner =>
    simp only [encode, CpOrderRateThresholdChangeRequestMessage.encode_length]
    omega
  | cpClearAllBreachesRequestMessage inner =>
    simp only [encode, CpClearAllBreachesRequestMessage.encode_length]
    omega
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage inner =>
    simp only [encode, CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgeAllRequestMessage inner =>
    simp only [encode, ActiveRiskAcknowledgeAllRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 1 then (RiskSettingsQueryMessage.decode bytes).map fun (message, rest) => (.riskSettingsQueryMessage message, rest)
  else if tag = 2 then (ActiveRiskThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskThresholdChangeRequestMessage message, rest)
  else if tag = 3 then (ActiveRiskAcknowledgementRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgementRequestMessage message, rest)
  else if tag = 4 then (CpVolumeThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpVolumeThresholdChangeRequestMessage message, rest)
  else if tag = 5 then (CpExecutedNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpExecutedNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 6 then (CpTotalExecutionsThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpTotalExecutionsThresholdChangeRequestMessage message, rest)
  else if tag = 7 then (CpPercentOutstandingContractsThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpPercentOutstandingContractsThresholdChangeRequestMessage message, rest)
  else if tag = 8 then (CpBreachCountThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpBreachCountThresholdChangeRequestMessage message, rest)
  else if tag = 9 then (ManualCpBreachTriggerRequestMessage.decode bytes).map fun (message, rest) => (.manualCpBreachTriggerRequestMessage message, rest)
  else if tag = 10 then (CpClearBreachRequestMessage.decode bytes).map fun (message, rest) => (.cpClearBreachRequestMessage message, rest)
  else if tag = 11 then (SingleOrderAllowIsoOrdersChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowIsoOrdersChangeRequestMessage message, rest)
  else if tag = 12 then (SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowOrdersInCrossedMarketChangeRequestMessage message, rest)
  else if tag = 13 then (SingleOrderMaxNotionalChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxNotionalChangeRequestMessage message, rest)
  else if tag = 14 then (SingleOrderMaxContractsChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderMaxContractsChangeRequestMessage message, rest)
  else if tag = 15 then (SingleOrderAllowMarketOrdersChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderAllowMarketOrdersChangeRequestMessage message, rest)
  else if tag = 16 then (SingleOrderRestrictedUnderlierChangeRequestMessage.decode bytes).map fun (message, rest) => (.singleOrderRestrictedUnderlierChangeRequestMessage message, rest)
  else if tag = 18 then (CpGrossNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpGrossNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 19 then (CpMarketOrderGrossNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderGrossNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 20 then (CpNetNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpNetNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 21 then (CpMarketOrderNetNotionalThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpMarketOrderNetNotionalThresholdChangeRequestMessage message, rest)
  else if tag = 22 then (CpDuplicateOrderThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpDuplicateOrderThresholdChangeRequestMessage message, rest)
  else if tag = 23 then (CpOrderRateThresholdChangeRequestMessage.decode bytes).map fun (message, rest) => (.cpOrderRateThresholdChangeRequestMessage message, rest)
  else if tag = 24 then (CpClearAllBreachesRequestMessage.decode bytes).map fun (message, rest) => (.cpClearAllBreachesRequestMessage message, rest)
  else if tag = 25 then (CpClearAllBreachesByEfidOrUnderlierRequestMessage.decode bytes).map fun (message, rest) => (.cpClearAllBreachesByEfidOrUnderlierRequestMessage message, rest)
  else if tag = 26 then (ActiveRiskAcknowledgeAllRequestMessage.decode bytes).map fun (message, rest) => (.activeRiskAcknowledgeAllRequestMessage message, rest)
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
  | activeRiskThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskThresholdChangeRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgementRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgementRequestMessage.encode_length]
    omega
  | cpVolumeThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpVolumeThresholdChangeRequestMessage.encode_length]
    omega
  | cpExecutedNotionalThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpExecutedNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpTotalExecutionsThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpTotalExecutionsThresholdChangeRequestMessage.encode_length]
    omega
  | cpPercentOutstandingContractsThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpPercentOutstandingContractsThresholdChangeRequestMessage.encode_length]
    omega
  | cpBreachCountThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpBreachCountThresholdChangeRequestMessage.encode_length]
    omega
  | manualCpBreachTriggerRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ManualCpBreachTriggerRequestMessage.encode_length]
    omega
  | cpClearBreachRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearBreachRequestMessage.encode_length]
    omega
  | singleOrderAllowIsoOrdersChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowIsoOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowOrdersInCrossedMarketChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowOrdersInCrossedMarketChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxNotionalChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxNotionalChangeRequestMessage.encode_length]
    omega
  | singleOrderMaxContractsChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderMaxContractsChangeRequestMessage.encode_length]
    omega
  | singleOrderAllowMarketOrdersChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderAllowMarketOrdersChangeRequestMessage.encode_length]
    omega
  | singleOrderRestrictedUnderlierChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SingleOrderRestrictedUnderlierChangeRequestMessage.encode_length]
    omega
  | cpGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderGrossNotionalThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderGrossNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpNetNotionalThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpMarketOrderNetNotionalThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpMarketOrderNetNotionalThresholdChangeRequestMessage.encode_length]
    omega
  | cpDuplicateOrderThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpDuplicateOrderThresholdChangeRequestMessage.encode_length]
    omega
  | cpOrderRateThresholdChangeRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpOrderRateThresholdChangeRequestMessage.encode_length]
    omega
  | cpClearAllBreachesRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearAllBreachesRequestMessage.encode_length]
    omega
  | cpClearAllBreachesByEfidOrUnderlierRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CpClearAllBreachesByEfidOrUnderlierRequestMessage.encode_length]
    omega
  | activeRiskAcknowledgeAllRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ActiveRiskAcknowledgeAllRequestMessage.encode_length]
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

end Omi.MemxMemxoptionsRiskcontrolSbeV17Client
