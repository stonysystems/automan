import matplotlib.pyplot as plt
import re
import os

def parse_figure8_data(file_path):
  """Parse throughput and latency data from Figure8 txt files"""
  throughputs = []
  latencies = []
  
  with open(file_path, 'r') as f:
    for line in f:
      if 'Throughput' in line and 'avg latency ms' in line:
        throughput_match = re.search(r'Throughput (\d+)', line)
        latency_match = re.search(r'avg latency ms ([\d.]+)', line)
        
        if throughput_match and latency_match:
          throughputs.append(int(throughput_match.group(1)))
          latencies.append(float(latency_match.group(1)))
  
  return throughputs, latencies

def create_figure8_plot():
  """Create Figure 8 with two subplots showing throughput vs latency"""
  
  # Data directory
  data_dir = 'Figure8'
  
  # Parse data from all files
  systems = {
    'AutoManPBFT-I0': 'AutoManPBFT-I0.txt',
    'AutoManPBFT-I1': 'AutoManPBFT-I1.txt', 
    'AutoManRSL-I0': 'AutoManRSL-I0.txt',
    'AutoManRSL-I1': 'AutoManRSL-I1.txt',
    'IronRSL': 'IronRSL.txt'
  }
  
  data = {}
  for system, filename in systems.items():
    file_path = os.path.join(data_dir, filename)
    if os.path.exists(file_path):
      throughputs, latencies = parse_figure8_data(file_path)
      # Convert throughput to kilo reqs/s
      throughputs_kilo = [t/1000 for t in throughputs]
      data[system] = (throughputs_kilo, latencies)
  
  # Create figure with two subplots
  fig, (ax_a, ax_b) = plt.subplots(1, 2, figsize=(10, 4))
  
  # Define colors and markers for different systems (High contrast palette with cyan)
  styles = {
    'AutoManPBFT-I0': {'color': '#2D8B8B', 'marker': 'o', 'linestyle': '-'},
    'AutoManPBFT-I1': {'color': '#D2691E', 'marker': 's', 'linestyle': '--'},
    'AutoManRSL-I0': {'color': '#1F6B6B', 'marker': '^', 'linestyle': '-'},
    'AutoManRSL-I1': {'color': '#8B4513', 'marker': 'v', 'linestyle': '--'},
    'IronRSL': {'color': '#B22222', 'marker': 'd', 'linestyle': ':'}
  }
  
  # Plot (a) - Left subplot: RSL systems (Multi-Paxos)
  rsl_systems = ['AutoManRSL-I0', 'AutoManRSL-I1', 'IronRSL']
  for system in rsl_systems:
    if system in data:
      throughputs, latencies = data[system]
      ax_a.plot(throughputs, latencies,
           label=system,
           color=styles[system]['color'],
           marker=styles[system]['marker'],
           linestyle=styles[system]['linestyle'],
           markersize=8, linewidth=2)
  
  ax_a.set_xlabel('Throughput (kilo reqs/s)', fontsize=12)
  ax_a.set_ylabel('Latency (ms)', fontsize=12)
  ax_a.set_title('Multi-Paxos', fontsize=14, fontweight='bold', pad=-30)
  ax_a.grid(True, alpha=0.3)
  ax_a.legend(fontsize=10)
  ax_a.set_yscale('log')
  ax_a.yaxis.set_major_formatter(plt.FuncFormatter(lambda x, _: f'{x:.0f}'))
  
  # Plot (b) - Right subplot: PBFT systems
  pbft_systems = ['AutoManPBFT-I0', 'AutoManPBFT-I1']
  for system in pbft_systems:
    if system in data:
      throughputs, latencies = data[system]
      ax_b.plot(throughputs, latencies, 
           label=system,
           color=styles[system]['color'],
           marker=styles[system]['marker'],
           linestyle=styles[system]['linestyle'],
           markersize=8, linewidth=2)
  
  ax_b.set_xlabel('Throughput (kilo reqs/s)', fontsize=12)
  ax_b.set_ylabel('Latency (ms)', fontsize=12)
  ax_b.set_title('PBFT', fontsize=14, fontweight='bold', pad=-30)
  ax_b.grid(True, alpha=0.3)
  ax_b.legend(fontsize=10)
  ax_b.set_yscale('log')
  ax_b.yaxis.set_major_formatter(plt.FuncFormatter(lambda x, _: f'{x:.0f}'))
  
  # Adjust layout
  plt.tight_layout()
  
  # Save the figure
  plt.savefig('fig8.pdf', bbox_inches='tight')
  
  # Print data summary
  print("Data Summary:")
  for system, (throughputs, latencies) in data.items():
    print(f"{system}: {len(throughputs)} data points")
    if throughputs and latencies:
      print(f"  Throughput range: {min(throughputs):.1f} - {max(throughputs):.1f} kilo reqs/s")
      print(f"  Latency range: {min(latencies):.3f} - {max(latencies):.3f} ms")

if __name__ == "__main__":
  create_figure8_plot()