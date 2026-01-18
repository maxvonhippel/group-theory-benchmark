// OpenAI client configuration
client<llm> GPT4o {
  provider openai
  options {
    model "gpt-5.2"
    api_key env.OPENAI_API_KEY
  }
}