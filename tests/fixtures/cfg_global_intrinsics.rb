def global_contracts
  T.reveal_type(block_given?) # note: Revealed type: `T::Boolean`
  T.reveal_type(Integer("1")) # note: Revealed type: `Integer`
  T.reveal_type(to_enum(:each)) # note: Revealed type: `Enumerator`
  T.reveal_type(binding) # note: Revealed type: `Binding`
end
