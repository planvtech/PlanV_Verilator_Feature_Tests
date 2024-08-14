import os
from jinja2 import Template
import sys
from collections import defaultdict

# Get the current directory and branch name from command line arguments
current_dir = os.getcwd()
branch_name = sys.argv[1] if len(sys.argv) > 1 else "master"

# Define base log directory and report file path
base_log_dir = os.path.abspath(os.path.join(current_dir, "..", "logs", "feature_tests"))
report_file_path = os.path.join(base_log_dir, "tests_report.log")
logo_path = "planv_logo.png"  # Using a relative path assuming logo is in the same directory as the script

# Read the report file and process the data
data = defaultdict(lambda: {'PASSED': [], 'FAILED': []})
with open(report_file_path, "r") as report_file:
    for line in report_file:
        if line.strip() in ["Feature Tests Report", "============"]:
            continue
        if line.strip():
            test_name, status = line.split(": ")
            status = status.strip()
            category = test_name.split("/")[0]
            relative_log_file_path = os.path.join(test_name.replace("/", os.path.sep)) + ".log"
            data[category][status].append({"Test Name": test_name, "Log File": relative_log_file_path})

# Define the HTML template with the PlanV logo
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
        .category { margin-top: 40px; }
    </style>
</head>
<body>
    <img src="{{ logo_path }}" alt="PlanV Logo" style="width:150px;">
    <h1>Feature Test Report</h1>
    {% for category, tests in data.items() %}
    <div class="category">
        <h2>{{ category }}</h2>
        <p>Passed: {{ tests['PASSED']|length }}</p>
        <p>Failed: {{ tests['FAILED']|length }}</p>
        <table>
            <tr>
                <th>Test Name</th>
                <th>Status</th>
            </tr>
            {% for test in tests['PASSED'] %}
            <tr>
                <td><a href="{{ test['Log File'] }}">{{ test['Test Name'] }}</a></td>
                <td class="PASSED">PASSED</td>
            </tr>
            {% endfor %}
            {% for test in tests['FAILED'] %}
            <tr>
                <td><a href="{{ test['Log File'] }}">{{ test['Test Name'] }}</a></td>
                <td class="FAILED">FAILED</td>
            </tr>
            {% endfor %}
        </table>
    </div>
    {% endfor %}
</body>
</html>
"""

# Render the HTML content
template = Template(html_template)
html_content = template.render(data=data, logo_path=logo_path)

# Define the output HTML path, should be at the same level as 'logs'
output_html_path = os.path.abspath(os.path.join(base_log_dir, f"fancy_test_report_{branch_name}.html"))
with open(output_html_path, "w") as file:
    file.write(html_content)

print(f"HTML report generated as {output_html_path}")