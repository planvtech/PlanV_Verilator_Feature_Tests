import os
from jinja2 import Template
import sys

# Get the current directory and branch name from command line arguments
current_dir = os.getcwd()
branch_name = sys.argv[1] if len(sys.argv) > 1 else "master"

# Define base log directory and report file path
base_log_dir = os.path.abspath(os.path.join(current_dir, "..", "logs", "feature_tests"))
report_file_path = os.path.join(base_log_dir, "tests_report.log")

# Read the report file and process the data
data = []
with open(report_file_path, "r") as report_file:
    for line in report_file:
        if line.strip() == "Feature Tests Report" or line.strip() == "============":
            continue
        if line.strip():
            test_name, status = line.split(": ")
            status = status.strip()
            log_file_path = os.path.join(base_log_dir, test_name.replace("/", os.path.sep)) + ".log"
            data.append({"Test Name": test_name, "Status": status, "Log File": log_file_path})

# Define the HTML template
html_template = """
<!DOCTYPE html>
<html>
<head>
    <title>Test Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 40px; }
        table { width: 100%; border-collapse: collapse; }
        th, td { padding: 8px 12px; border: 1px solid #ccc; text-align: left; }
        th { background-color: #f4f4f4; }
        .PASSED { color: green; }
        .FAILED { color: red; }
    </style>
</head>
<body>
    <h1>Feature Test Report</h1>
    <table>
        <tr>
            <th>Test Name</th>
            <th>Status</th>
        </tr>
        {% for row in rows %}
        <tr>
            <td><a href="{{ row['Log File'] }}">{{ row['Test Name'] }}</a></td>
            <td class="{{ row['Status'] }}">{{ row['Status'] }}</td>
        </tr>
        {% endfor %}
    </table>
</body>
</html>
"""

# Render the HTML content
template = Template(html_template)
html_content = template.render(rows=data)

# Define the output HTML path, should be at the same level as 'logs'
output_html_path = os.path.abspath(os.path.join(base_log_dir, f"fancy_test_report_{branch_name}.html"))
with open(output_html_path, "w") as file:
    file.write(html_content)

print(f"HTML report generated as {output_html_path}")