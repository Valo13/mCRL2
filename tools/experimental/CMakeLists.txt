set(MCRL2_TOOLS
  besconvert  
  lpscleave
  lpscombine
  lpsrealelm
  lpsstategraph
  lpssymbolicbisim
  ltscompare2mcf
  pbesabsinthe
  pbespareqelm
  pbespor
  pbessymbolicbisim
  symbolic_exploration
)

if(MCRL2_ENABLE_EXPERIMENTAL)
  foreach(TOOL ${MCRL2_TOOLS})
    add_subdirectory(${TOOL})
  endforeach()
endif()
