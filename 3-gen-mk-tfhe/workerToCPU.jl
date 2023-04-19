using Distributed
using Hwloc

# Start some worker processes
addprocs(4)

# Load hardware topology information
topology = hwloc_topology_load()

# Get the CPU core where each worker process is running
for pid in workers()
    cpuset = hwloc_cpuset_t()
    hwloc_get_last_cpu_location(topology, cpuset, pid-1, HWLOC_CPUBIND_PROCESS)
    core = hwloc_cpuset_first(cpuset)
    println("Worker $pid is running on CPU core $core")
end
