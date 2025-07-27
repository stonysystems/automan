import matplotlib.pyplot as plt
import numpy as np
import os

def parse_figure9_data(file_path):
  """Parse time series data from Figure9 txt files"""
  data = []
  
  with open(file_path, 'r') as f:
    for line in f:
      line = line.strip()
      if line:
        try:
          value = float(line)
          data.append(value)
        except ValueError:
          continue
  
  return data

def create_figure9_plot():
  """Create Figure 9 with time series plots showing system performance over time"""
  
  # Data directory
  data_dir = 'Figure9'
  
  # Systems
  systems = {
    'AutoManRSL-I0': 'AutoManRSL-I0.txt',
    'AutoManRSL-I1': 'AutoManRSL-I1.txt',
    'IronRSL': 'IronRSL.txt'
  }
  
  # Create single figure
  plt.figure(figsize=(6, 4))
  
  # Define colors and line styles for different systems
  styles = {
    'AutoManRSL-I0': {'color': '#2D8B8B', 'linestyle': '-', 'linewidth': 1.5},
    'AutoManRSL-I1': {'color': '#D2691E', 'linestyle': '--', 'linewidth': 1.5},
    'IronRSL': {'color': '#B22222', 'linestyle': ':', 'linewidth': 2}
  }
  
  # Collect data for all systems
  system_data = {}
  for system, filename in systems.items():
    file_path = os.path.join(data_dir, filename)
    if os.path.exists(file_path):
      data = parse_figure9_data(file_path)
      if data:
        system_data[system] = data
  
  # Set time range to 400-1000 data points
  start_time = 400
  end_time = 1000
  
  for system, data in system_data.items():
    if len(data) > start_time:
      time_slice = data[start_time:min(end_time, len(data))]
      # Data is already in kilo units
      time_slice_kilo = time_slice
      # Time is in 10ms intervals, convert to seconds
      time_points_s = np.arange(start_time * 0.01, (start_time + len(time_slice)) * 0.01, 0.01)
      
      plt.plot(time_points_s, time_slice_kilo,
               label=system,
               color=styles[system]['color'],
               linestyle=styles[system]['linestyle'],
               linewidth=styles[system]['linewidth'])
  
  plt.xlabel('Time (s)', fontsize=12)
  plt.ylabel('Throughput (kilo reqs/s)', fontsize=12)
  plt.grid(True, alpha=0.3)
  plt.legend(fontsize=10)
  
  # Set axis limits
  plt.xlim(start_time * 0.01, end_time * 0.01)
  plt.ylim(0, 25)
  
  # Adjust layout
  plt.tight_layout()
  
  # Save the figure
  plt.savefig('fig9.pdf', bbox_inches='tight')
  
  # Print data summary
  print("Figure 9 Data Summary:")
  for system, data in system_data.items():
    if data:
      non_zero_data = [x for x in data if x > 0]
      print(f"\n{system}:")
      print(f"  Total data points: {len(data)}")
      print(f"  Non-zero data points: {len(non_zero_data)}")
      if non_zero_data:
        print(f"  Value range: {min(non_zero_data):.1f} - {max(non_zero_data):.1f}")
        print(f"  Average (non-zero): {np.mean(non_zero_data):.1f}")

if __name__ == "__main__":
  create_figure9_plot()