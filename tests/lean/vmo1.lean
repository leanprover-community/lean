meta def cheese : string := "edam"
meta def fromage : string := "comte"
#eval cheese
attribute [vm_override fromage] cheese
#eval cheese