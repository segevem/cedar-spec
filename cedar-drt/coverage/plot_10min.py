import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
fuzzer=[(30,22.26),(60,22.26),(90,22.26),(120,22.26),(150,30.87),(180,47.03),(210,49.71),(240,54.05),(270,58.35),(300,64.49),(330,68.71),(360,72.01),(390,72.72),(420,73.89),(450,75.36),(480,76.86),(510,78.07),(540,79.62),(570,81.5),(600,81.54)]
fixed=[(30,66.86),(60,72.5),(90,73.92),(120,74.26),(150,75.39),(180,75.39),(210,77.56),(240,77.56),(270,77.56),(300,77.98),(330,77.98),(360,78.06),(390,78.06),(420,78.06),(450,78.06),(480,78.06),(510,78.06),(540,78.81),(570,78.81),(600,78.81)]
growing=[(30,71.04),(60,74.68),(90,77.56),(120,77.56),(150,77.56),(180,77.98),(210,77.98),(240,78.06),(270,78.06),(300,78.06),(330,78.06),(360,78.06),(390,78.06),(420,78.27),(450,78.81),(480,78.81),(510,78.81),(540,78.81),(570,78.81),(600,78.81)]
fig,ax=plt.subplots(figsize=(11,6))
ax.plot(*zip(*fuzzer),'o-',color='tab:red',lw=2.5,ms=4,label='Fuzzer (feedback-driven)')
ax.plot(*zip(*fixed),'s-',color='tab:blue',lw=2.5,ms=4,label='Generator (fixed 64KB)')
ax.plot(*zip(*growing),'^--',color='tab:green',lw=2,ms=4,label='Generator (growing 32B -> 189KB)')
ax.set(xlabel='Time (seconds)',ylabel='Typechecker Coverage (%)',title='Typechecker Coverage Over Time (10 minutes each)',ylim=(0,100),xlim=(0,640))
ax.annotate('81.5%',xy=(600,81.54),xytext=(610,83),fontsize=10,color='tab:red')
ax.annotate('78.8%',xy=(600,78.81),xytext=(610,76),fontsize=10,color='tab:blue')
ax.legend(fontsize=10,loc='lower right'); ax.grid(alpha=0.3)
plt.tight_layout(); plt.savefig('coverage_comparison_10min.png',dpi=150); print('Saved')
