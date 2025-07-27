import matplotlib.pyplot as plt
import re
import os

def parse_figure12_data(file_path):
  """Parse throughput and latency data from Figure12 txt files"""
  data = {}
  
  with open(file_path, 'r') as f:
    for line in f:
      if 'clients num:' in line and 'throughput' in line and 'latency' in line:
        # Handle different formats
        if 'throughput:' in line:  # PGo-RaftKV format
          clients_match = re.search(r'clients num: (\d+)', line)
          throughput_match = re.search(r'throughput: ([\d.]+)', line)
          latency_match = re.search(r'avg latency: ([\d.]+)ms', line)
        else:  # AutoMan format
          clients_match = re.search(r'clients num: (\d+)', line)
          throughput_match = re.search(r'throughput (\d+)', line)
          latency_match = re.search(r'avg latency ms ([\d.]+)', line)
        
        if clients_match and throughput_match and latency_match:
          clients = int(clients_match.group(1))
          throughput = float(throughput_match.group(1))
          latency = float(latency_match.group(1))
          data[clients] = {'throughput': throughput, 'latency': latency}
  
  return data

def create_figure12_plot():
  """Create Figure 12 with throughput and latency comparison"""
  
  # Data directory
  data_dir = 'Figure12'
  
  # Systems
  systems = {
    'AutoMan-PaxosKV-I0': 'AutoMan-PaxosKV-I0.txt',
    'AutoMan-PaxosKV-I1': 'AutoMan-PaxosKV-I1.txt',
    'PGo-RaftKV': 'PGo-RaftKV.txt'
  }
  
  # Create single figure
  plt.figure(figsize=(5, 3))
  
  # Define colors and markers for different systems
  styles = {
    'AutoMan-PaxosKV-I0': {'color': '#2D8B8B', 'marker': 'o', 'linestyle': '-'},
    'AutoMan-PaxosKV-I1': {'color': '#D2691E', 'marker': 's', 'linestyle': '--'},
    'PGo-RaftKV': {'color': '#B22222', 'marker': '^', 'linestyle': ':'}
  }
  
  # Collect data for all systems
  system_data = {}
  for system, filename in systems.items():
    file_path = os.path.join(data_dir, filename)
    if os.path.exists(file_path):
      data = parse_figure12_data(file_path)
      if data:
        system_data[system] = data
  
  # Plot throughput vs latency
  for system, data in system_data.items():
    clients = sorted(data.keys())
    throughputs = [data[c]['throughput'] for c in clients]
    latencies = [data[c]['latency'] for c in clients]
    
    plt.plot(throughputs, latencies,
            label=system,
            color=styles[system]['color'],
            marker=styles[system]['marker'],
            linestyle=styles[system]['linestyle'],
            markersize=6, linewidth=2)
  
  plt.xlabel('Throughput (reqs/s)', fontsize=12)
  plt.ylabel('Latency (ms)', fontsize=12)
  plt.grid(True, alpha=0.3)
  plt.legend(fontsize=10)
  plt.xlim(left=200)
  plt.ylim(0, 20)
  
  # Set y-axis ticks for uniform intervals
  import numpy as np
  plt.yticks(np.arange(0, 21, 4))
  
  # Adjust layout
  plt.tight_layout()
  
  # Save the figure
  plt.savefig('fig12.pdf', bbox_inches='tight')
  
  # Print data summary
  print("Figure 12 Data Summary:")
  for system, data in system_data.items():
    clients_range = sorted(data.keys())
    throughputs = [data[c]['throughput'] for c in clients_range]
    latencies = [data[c]['latency'] for c in clients_range]
    print(f"\n{system}:")
    print(f"  Clients range: {min(clients_range)}-{max(clients_range)}")
    print(f"  {len(data)} data points")
    print(f"  Throughput range: {min(throughputs):.1f}-{max(throughputs):.1f} reqs/s")
    print(f"  Latency range: {min(latencies):.3f}-{max(latencies):.3f} ms")

if __name__ == "__main__":
  create_figure12_plot()