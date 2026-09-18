import Omi.Wire

/-!
# CME Group Market Data Platform 3 v1.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexMdp3SbeV19ClientTcp

/-- Client Technical Header: 14 bytes -/
structure ClientTechnicalHeader where
  encodingType : BitVec 16
  messageSequenceNumber : BitVec 32
  tcpSendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ClientTechnicalHeader

def encode (message : ClientTechnicalHeader) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ (encodeUIntLE 4 message.messageSequenceNumber
    ++ (encodeUIntLE 8 message.tcpSendingTime))

def decode (bytes : List UInt8) : Option (ClientTechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : ClientTechnicalHeader) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ClientTechnicalHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientTechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ClientTechnicalHeader

/-- Negotiate: 78 bytes -/
structure Negotiate where
  hmacSignature : Alpha 32
  accessKeyId : Alpha 20
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  session : Alpha 5
  firm : Alpha 5
  deriving DecidableEq, Repr

namespace Negotiate

def encode (message : Negotiate) : List UInt8 :=
  Alpha.encode message.hmacSignature
    ++ (Alpha.encode message.accessKeyId
    ++ (encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (Alpha.encode message.session
    ++ (Alpha.encode message.firm)))))

def decode (bytes : List UInt8) : Option (Negotiate × List UInt8) := do
  let (hmacSignature, bytes) ← Alpha.decode 32 bytes
  let (accessKeyId, bytes) ← Alpha.decode 20 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (session, bytes) ← Alpha.decode 5 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  pure ({ hmacSignature, accessKeyId, uuid, requestTimestamp, session, firm }, bytes)

@[simp] theorem encode_length (message : Negotiate) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : Negotiate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Negotiate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end Negotiate

/-- Terminate: 70 bytes -/
structure Terminate where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 8
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace Terminate

def encode (message : Terminate) : List UInt8 :=
  Alpha.encode message.reason
    ++ (encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.errorCodes
    ++ (Alpha.encode message.padding5))))

def decode (bytes : List UInt8) : Option (Terminate × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUInt 1 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, padding5 }, bytes)

@[simp] theorem encode_length (message : Terminate) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Terminate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Terminate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Terminate

/-- Market Data Request Security Group: 6 bytes -/
structure MarketDataRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroup

def encode (message : MarketDataRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : MarketDataRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDataRequestSecurityGroup

/-- Market Data Request Security Groups -/
structure MarketDataRequestSecurityGroups where
  blockLength : BitVec 16
  marketDataRequestSecurityGroup : Bounded 1 MarketDataRequestSecurityGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroups

def encode (message : MarketDataRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestSecurityGroup.val.length)
    ++ (encodeMany MarketDataRequestSecurityGroup.encode message.marketDataRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroup_, bytes) ← decodeMany MarketDataRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestSecurityGroup : marketDataRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestSecurityGroup := ⟨marketDataRequestSecurityGroup_, fits_marketDataRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_marketDataRequestSecurityGroup := message.marketDataRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestSecurityGroup.encode 6 MarketDataRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketDataRequestSecurityGroup.encode MarketDataRequestSecurityGroup.decode MarketDataRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDataRequestSecurityGroup.length_lt]
  rfl

end MarketDataRequestSecurityGroups

/-- Market Data Request Related Symbol Group: 4 bytes -/
structure MarketDataRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroup

def encode (message : MarketDataRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDataRequestRelatedSymbolGroup

/-- Market Data Request Related Symbol Groups -/
structure MarketDataRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  marketDataRequestRelatedSymbolGroup : Bounded 1 MarketDataRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroups

def encode (message : MarketDataRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany MarketDataRequestRelatedSymbolGroup.encode message.marketDataRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestRelatedSymbolGroup_, bytes) ← decodeMany MarketDataRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestRelatedSymbolGroup : marketDataRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestRelatedSymbolGroup := ⟨marketDataRequestRelatedSymbolGroup_, fits_marketDataRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_marketDataRequestRelatedSymbolGroup := message.marketDataRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestRelatedSymbolGroup.encode 4 MarketDataRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketDataRequestRelatedSymbolGroup.encode MarketDataRequestRelatedSymbolGroup.decode MarketDataRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDataRequestRelatedSymbolGroup.length_lt]
  rfl

end MarketDataRequestRelatedSymbolGroups

/-- Market Data Request -/
structure MarketDataRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  marketDataRequestSecurityGroups : MarketDataRequestSecurityGroups
  marketDataRequestRelatedSymbolGroups : MarketDataRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace MarketDataRequest

def encode (message : MarketDataRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (MarketDataRequestSecurityGroups.encode message.marketDataRequestSecurityGroups
    ++ (MarketDataRequestRelatedSymbolGroups.encode message.marketDataRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (MarketDataRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroups, bytes) ← MarketDataRequestSecurityGroups.decode bytes
  let (marketDataRequestRelatedSymbolGroups, bytes) ← MarketDataRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, marketDataRequestSecurityGroups, marketDataRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : MarketDataRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequest) : (encode message).length ≤ 2561 := by
  have bound_marketDataRequestSecurityGroups := MarketDataRequestSecurityGroups.encode_length_le message.marketDataRequestSecurityGroups
  have bound_marketDataRequestRelatedSymbolGroups := MarketDataRequestRelatedSymbolGroups.encode_length_le message.marketDataRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketDataRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [MarketDataRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end MarketDataRequest

/-- Security List Request Security Group: 6 bytes -/
structure SecurityListRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroup

def encode (message : SecurityListRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityListRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityListRequestSecurityGroup

/-- Security List Request Security Groups -/
structure SecurityListRequestSecurityGroups where
  blockLength : BitVec 16
  securityListRequestSecurityGroup : Bounded 1 SecurityListRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroups

def encode (message : SecurityListRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestSecurityGroup.val.length)
    ++ (encodeMany SecurityListRequestSecurityGroup.encode message.securityListRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroup_, bytes) ← decodeMany SecurityListRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestSecurityGroup : securityListRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestSecurityGroup := ⟨securityListRequestSecurityGroup_, fits_securityListRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityListRequestSecurityGroup := message.securityListRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestSecurityGroup.encode 6 SecurityListRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityListRequestSecurityGroup.encode SecurityListRequestSecurityGroup.decode SecurityListRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityListRequestSecurityGroup.length_lt]
  rfl

end SecurityListRequestSecurityGroups

/-- Security List Request Related Symbol Group: 4 bytes -/
structure SecurityListRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroup

def encode (message : SecurityListRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListRequestRelatedSymbolGroup

/-- Security List Request Related Symbol Groups -/
structure SecurityListRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityListRequestRelatedSymbolGroup : Bounded 1 SecurityListRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroups

def encode (message : SecurityListRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany SecurityListRequestRelatedSymbolGroup.encode message.securityListRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityListRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestRelatedSymbolGroup : securityListRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestRelatedSymbolGroup := ⟨securityListRequestRelatedSymbolGroup_, fits_securityListRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityListRequestRelatedSymbolGroup := message.securityListRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestRelatedSymbolGroup.encode 4 SecurityListRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityListRequestRelatedSymbolGroup.encode SecurityListRequestRelatedSymbolGroup.decode SecurityListRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityListRequestRelatedSymbolGroup.length_lt]
  rfl

end SecurityListRequestRelatedSymbolGroups

/-- Security List Request -/
structure SecurityListRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityListRequestSecurityGroups : SecurityListRequestSecurityGroups
  securityListRequestRelatedSymbolGroups : SecurityListRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityListRequest

def encode (message : SecurityListRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (SecurityListRequestSecurityGroups.encode message.securityListRequestSecurityGroups
    ++ (SecurityListRequestRelatedSymbolGroups.encode message.securityListRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (SecurityListRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroups, bytes) ← SecurityListRequestSecurityGroups.decode bytes
  let (securityListRequestRelatedSymbolGroups, bytes) ← SecurityListRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityListRequestSecurityGroups, securityListRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityListRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequest) : (encode message).length ≤ 2561 := by
  have bound_securityListRequestSecurityGroups := SecurityListRequestSecurityGroups.encode_length_le message.securityListRequestSecurityGroups
  have bound_securityListRequestRelatedSymbolGroups := SecurityListRequestRelatedSymbolGroups.encode_length_le message.securityListRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityListRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [SecurityListRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end SecurityListRequest

/-- Security Status Request Security Group: 6 bytes -/
structure SecurityStatusRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroup

def encode (message : SecurityStatusRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusRequestSecurityGroup

/-- Security Status Request Security Groups -/
structure SecurityStatusRequestSecurityGroups where
  blockLength : BitVec 16
  securityStatusRequestSecurityGroup : Bounded 1 SecurityStatusRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroups

def encode (message : SecurityStatusRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestSecurityGroup.val.length)
    ++ (encodeMany SecurityStatusRequestSecurityGroup.encode message.securityStatusRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroup_, bytes) ← decodeMany SecurityStatusRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestSecurityGroup : securityStatusRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestSecurityGroup := ⟨securityStatusRequestSecurityGroup_, fits_securityStatusRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityStatusRequestSecurityGroup := message.securityStatusRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestSecurityGroup.encode 6 SecurityStatusRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityStatusRequestSecurityGroup.encode SecurityStatusRequestSecurityGroup.decode SecurityStatusRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusRequestSecurityGroup.length_lt]
  rfl

end SecurityStatusRequestSecurityGroups

/-- Security Status Request Related Symbol Group: 4 bytes -/
structure SecurityStatusRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroup

def encode (message : SecurityStatusRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusRequestRelatedSymbolGroup

/-- Security Status Request Related Symbol Groups -/
structure SecurityStatusRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityStatusRequestRelatedSymbolGroup : Bounded 1 SecurityStatusRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroups

def encode (message : SecurityStatusRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany SecurityStatusRequestRelatedSymbolGroup.encode message.securityStatusRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityStatusRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestRelatedSymbolGroup : securityStatusRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestRelatedSymbolGroup := ⟨securityStatusRequestRelatedSymbolGroup_, fits_securityStatusRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityStatusRequestRelatedSymbolGroup := message.securityStatusRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestRelatedSymbolGroup.encode 4 SecurityStatusRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityStatusRequestRelatedSymbolGroup.encode SecurityStatusRequestRelatedSymbolGroup.decode SecurityStatusRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusRequestRelatedSymbolGroup.length_lt]
  rfl

end SecurityStatusRequestRelatedSymbolGroups

/-- Security Status Request -/
structure SecurityStatusRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityStatusRequestSecurityGroups : SecurityStatusRequestSecurityGroups
  securityStatusRequestRelatedSymbolGroups : SecurityStatusRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityStatusRequest

def encode (message : SecurityStatusRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (SecurityStatusRequestSecurityGroups.encode message.securityStatusRequestSecurityGroups
    ++ (SecurityStatusRequestRelatedSymbolGroups.encode message.securityStatusRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (SecurityStatusRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroups, bytes) ← SecurityStatusRequestSecurityGroups.decode bytes
  let (securityStatusRequestRelatedSymbolGroups, bytes) ← SecurityStatusRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityStatusRequestSecurityGroups, securityStatusRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityStatusRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequest) : (encode message).length ≤ 2561 := by
  have bound_securityStatusRequestSecurityGroups := SecurityStatusRequestSecurityGroups.encode_length_le message.securityStatusRequestSecurityGroups
  have bound_securityStatusRequestRelatedSymbolGroups := SecurityStatusRequestRelatedSymbolGroups.encode_length_le message.securityStatusRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [SecurityStatusRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end SecurityStatusRequest

/-- Subscriber Heartbeat: 0 bytes -/
structure SubscriberHeartbeat where
  deriving DecidableEq, Repr

namespace SubscriberHeartbeat

def encode (_ : SubscriberHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SubscriberHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SubscriberHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SubscriberHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SubscriberHeartbeat

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | negotiate (message : Negotiate) -- 200
  | terminate (message : Terminate) -- 203
  | marketDataRequest (message : MarketDataRequest) -- 205
  | securityListRequest (message : SecurityListRequest) -- 208
  | securityStatusRequest (message : SecurityStatusRequest) -- 209
  | subscriberHeartbeat (message : SubscriberHeartbeat) -- 210
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .negotiate _ => 200
  | .terminate _ => 203
  | .marketDataRequest _ => 205
  | .securityListRequest _ => 208
  | .securityStatusRequest _ => 209
  | .subscriberHeartbeat _ => 210

def encode : ClientPayload → List UInt8
  | .negotiate message => Negotiate.encode message
  | .terminate message => Terminate.encode message
  | .marketDataRequest message => MarketDataRequest.encode message
  | .securityListRequest message => SecurityListRequest.encode message
  | .securityStatusRequest message => SecurityStatusRequest.encode message
  | .subscriberHeartbeat message => SubscriberHeartbeat.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 200 then (Negotiate.decode bytes).map fun (message, rest) => (.negotiate message, rest)
  else if tag = 203 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 205 then (MarketDataRequest.decode bytes).map fun (message, rest) => (.marketDataRequest message, rest)
  else if tag = 208 then (SecurityListRequest.decode bytes).map fun (message, rest) => (.securityListRequest message, rest)
  else if tag = 209 then (SecurityStatusRequest.decode bytes).map fun (message, rest) => (.securityStatusRequest message, rest)
  else if tag = 210 then (SubscriberHeartbeat.decode bytes).map fun (message, rest) => (.subscriberHeartbeat message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Tcp Message -/
structure ClientTcpMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientTcpMessage

def encodeBody (message : ClientTcpMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (ClientPayload.tag message.clientPayload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (ClientPayload.encode message.clientPayload))))

def decodeBody (bytes : List UInt8) : Option (ClientTcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientTcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientTcpMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | negotiate inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Negotiate.encode_length]
    omega
  | terminate inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Terminate.encode_length]
    omega
  | marketDataRequest inner =>
    have bound_inner := MarketDataRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityListRequest inner =>
    have bound_inner := SecurityListRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityStatusRequest inner =>
    have bound_inner := SecurityStatusRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | subscriberHeartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SubscriberHeartbeat.encode_length]
    omega

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : ClientTcpMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (ClientTcpMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : ClientTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientTcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientTcpMessage

/-- Client Tcp Packet -/
structure ClientTcpPacket where
  clientTechnicalHeader : ClientTechnicalHeader
  clientTcpMessage : List ClientTcpMessage
  deriving DecidableEq, Repr

namespace ClientTcpPacket

def encode (message : ClientTcpPacket) : List UInt8 :=
  ClientTechnicalHeader.encode message.clientTechnicalHeader
    ++ (encodeMany ClientTcpMessage.encode message.clientTcpMessage)

def decode (bytes : List UInt8) : Option ClientTcpPacket := do
  let (clientTechnicalHeader, bytes) ← ClientTechnicalHeader.decode bytes
  let clientTcpMessage ← decodeAll ClientTcpMessage.decode bytes.length bytes
  pure { clientTechnicalHeader, clientTcpMessage }

theorem encode_length_pos (message : ClientTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [ClientTechnicalHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : ClientTcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [ClientTechnicalHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany ClientTcpMessage.encode ClientTcpMessage.decode ClientTcpMessage.decode_encode ClientTcpMessage.encode_length_pos message.clientTcpMessage _ (encodeMany_length_ge ClientTcpMessage.encode ClientTcpMessage.encode_length_pos message.clientTcpMessage), some_bind]
  rfl

end ClientTcpPacket

end Omi.CmeGlobexMdp3SbeV19ClientTcp
