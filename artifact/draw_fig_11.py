import matplotlib.pyplot as plt
import re
import os

def parse_figure11_data(file_path):
  """Parse throughput and latency data from Figure11 txt files"""
  data = {}
  
  with open(file_path, 'r') as f:
    for line in f:
      if 'nthreads=' in line and 'Throughput' in line and 'avg latency ms' in line:
        threads_match = re.search(r'nthreads=(\d+)', line)
        throughput_match = re.search(r'Throughput (\d+)', line)
        latency_match = re.search(r'avg latency ms ([\d.]+)', line)
        
        if threads_match and throughput_match and latency_match:
          threads = int(threads_match.group(1))
          throughput = int(throughput_match.group(1))
          latency = float(latency_match.group(1))
          data[threads] = {'throughput': throughput, 'latency': latency}
  
  return data

def create_figure11_plot():
  """Create Figure 11 with grouped bar charts showing Key-Value store performance"""
  
  # Data directory
  data_dir = 'Figure11'
  
  # Systems and operations
  systems = ['AutoManKV-I0', 'AutoManKV-I1', 'IronKV']
  operations = ['get', 'set']
  value_sizes = ['128', '1024', '8192']
  thread_counts = [1, 4, 16, 32]
  
  # Create figure with 2x3 subplots (2 operations x 3 value sizes)
  fig, axes = plt.subplots(2, 3, figsize=(12, 6))
  
  # Define colors for different systems
  colors = {
    'AutoManKV-I0': '#2D8B8B',
    'AutoManKV-I1': '#D2691E',
    'IronKV': '#B22222'
  }
  
  # Plot data for each operation and value size
  for op_idx, operation in enumerate(operations):
    for size_idx, value_size in enumerate(value_sizes):
      ax = axes[op_idx, size_idx]
      
      # Collect throughput data for all systems and thread counts
      system_throughputs = {system: [] for system in systems}
      
      for system in systems:
        filename = f"{operation}-{value_size}.txt"
        file_path = os.path.join(data_dir, system, filename)
        
        if os.path.exists(file_path):
          data = parse_figure11_data(file_path)
          for threads in thread_counts:
            if threads in data:
              # Convert to kilo reqs/s
              throughput_kilo = data[threads]['throughput'] / 1000
              system_throughputs[system].append(throughput_kilo)
            else:
              system_throughputs[system].append(0)
        else:
          system_throughputs[system] = [0] * len(thread_counts)
      
      # Create grouped bar chart
      x = range(len(thread_counts))
      width = 0.25
      
      for i, system in enumerate(systems):
        x_pos = [pos + i * width for pos in x]
        ax.bar(x_pos, system_throughputs[system], width,
               label=system, color=colors[system], alpha=0.8)
      
      # Set labels and title
      ax.set_xlabel('Number of Clients', fontsize=10)
      ax.set_ylabel('Throughput (kilo reqs/s)', fontsize=10)
      
      # Set title based on operation and value size
      if value_size == '128':
        size_label = '128B'
      elif value_size == '1024':
        size_label = '1KB'
      elif value_size == '8192':
        size_label = '8KB'
      else:
        size_label = f'{value_size}B'
      
      ax.set_title(f'{operation.capitalize()}-{size_label}', fontsize=11, fontweight='bold')
      
      # Set x-axis ticks and labels for thread counts
      ax.set_xticks([pos + width for pos in x])
      ax.set_xticklabels(thread_counts)
      ax.grid(True, alpha=0.3, axis='y')
      
      # Set y-axis range from 0 to 50
      ax.set_ylim(0, 50)
  
  # Create a single legend for all subplots at the top
  handles, labels = axes[0, 0].get_legend_handles_labels()
  fig.legend(handles, labels, loc='upper center', bbox_to_anchor=(0.5, 0.95), ncol=3, fontsize=10)
  
  # Adjust layout
  plt.tight_layout()
  
  # Save the figure
  plt.savefig('fig11.pdf', bbox_inches='tight')
  
  # Print data summary
  print("Figure 11 Data Summary:")
  for system in systems:
    print(f"\n{system}:")
    for operation in operations:
      for value_size in value_sizes:
        filename = f"{operation}-{value_size}.txt"
        file_path = os.path.join(data_dir, system, filename)
        if os.path.exists(file_path):
          data = parse_figure11_data(file_path)
          if data:
            throughputs = [data[threads]['throughput']/1000 for threads in sorted(data.keys())]
            latencies = [data[threads]['latency'] for threads in sorted(data.keys())]
            print(f"  {operation}-{value_size}B: {len(data)} points, "
                f"Throughput: {min(throughputs):.1f}-{max(throughputs):.1f} kreqs/s, "
                f"Latency: {min(latencies):.3f}-{max(latencies):.3f} ms")

if __name__ == "__main__":
  create_figure11_plot()